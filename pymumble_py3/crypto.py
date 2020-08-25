'''
OCB2 crypto, broadly following the implementation from Mumble
'''
import struct
import time
from math import ceil

import Crypto
import Crypto.Random


AES_BLOCK_SIZE = 128 // 8
AES_KEY_SIZE_BITS = 128
AES_KEY_SIZE_BYTES = AES_KEY_SIZE_BITS // 8
SHIFTBITS = 63
MAX64 = (1 << 64) - 1


class EncryptFailedException(Exception):
    pass


class DecryptFailedException(Exception):
    pass


class CryptStateOCB2:
    def __init__(self):
        self.uiGood = 0
        self.uiLate = 0
        self.uiLost = 0
        self.tLastGood = 0

        self._raw_key = Crypto.Random.get_random_bytes(AES_KEY_SIZE_BYTES)
        self._encrypt_iv = Crypto.Random.get_random_bytes(AES_BLOCK_SIZE)
        self._decrypt_iv = Crypto.Random.get_random_bytes(AES_BLOCK_SIZE)
        self._aes = None
        self.decrypt_history = [0] * 0x100

    @property
    def raw_key(self) -> bytes:
        return self._raw_key

    @raw_key.setter
    def raw_key(self, rkey: bytes):
        if len(rkey) != AES_KEY_SIZE_BYTES:
            raise Exception('raw_key has long length')
        self._raw_key = bytes(rkey)
        self._aes = Crypto.Cipher.AES.new(key=self.raw_key, mode=Crypto.Cipher.AES.MODE_ECB)

    @property
    def encrypt_iv(self) -> bytearray:
        return self._encrypt_iv

    @encrypt_iv.setter
    def encrypt_iv(self, eiv: bytearray):
        if len(eiv) != AES_BLOCK_SIZE:
            raise Exception('encrypt_iv has long length')
        self._encrypt_iv = bytearray(eiv)

    @property
    def decrypt_iv(self) -> bytearray:
        return self._decrypt_iv

    @decrypt_iv.setter
    def decrypt_iv(self, div: bytearray):
        if len(div) != AES_BLOCK_SIZE:
            raise Exception('decrypt_iv has long length')
        self._decrypt_iv = bytearray(div)

    def is_valid(self) -> bool:
        return self._aes is not None

    def gen_key(self):
        self.raw_key = Crypto.Random.get_random_bytes(AES_KEY_SIZE_BYTES)
        self.encrypt_iv = Crypto.Random.get_random_bytes(AES_BLOCK_SIZE)
        self.decrypt_iv = Crypto.Random.get_random_bytes(AES_BLOCK_SIZE)

    def set_key(self, rkey: bytes, eiv: bytes, div: bytes):
        self.raw_key = rkey
        self.encrypt_iv = eiv
        self.decrypt_iv = div

    def encrypt(self, source: bytes) -> bytes:
        # First, increase our IV.
        eiv = increment_iv(self.encrypt_iv)
        self.encrypt_iv = eiv

        dst, tag = ocb_encrypt(self._aes, source, bytes(eiv))

        head = bytes((eiv[0], *tag[:3]))
        return head + dst

    def decrypt(self, source: bytes, len_plain: int) -> bytes:
        if len(source) < 4:
            raise DecryptFailedException('Source <4 bytes long!')

        div = self.decrypt_iv.copy()
        ivbyte = source[0]
        late = False
        lost = 0

        if (div[0] + 1) & 0xFF == ivbyte:
            # In order as expected.
            if ivbyte > div[0]:
                div[0] = ivbyte
            elif ivbyte < div[0]:
                div[0] = ivbyte
                div = increment_iv(div, 1)
            else:
                raise DecryptFailedException('ivbyte == decrypt_iv[0]')
        else:
            # This is either out of order or a repeat.
            diff = ivbyte - div[0]
            if diff > 128:
                diff -= 256
            elif diff < -128:
                diff += 256

            if ivbyte < div[0] and -30 < diff < 0:
                # Late packet, but no wraparound.
                late = True
                lost = -1
                div[0] = ivbyte
            elif ivbyte > div[0] and -30 < diff < 0:
                # Last was 0x02, here comes 0xff from last round
                late = True
                lost = -1
                div[0] = ivbyte
                div = decrement_iv(div, 1)
            elif ivbyte > div[0] and diff > 0:
                # Lost a few packets, but beyond that we're good.
                lost = ivbyte - div[0] - 1
                div[0] = ivbyte
            elif ivbyte < div[0] and diff > 0:
                # Lost a few packets, and wrapped around
                lost = 0x100 - div[0] + ivbyte - 1
                div[0] = ivbyte
                div = increment_iv(div, 1)
            else:
                raise DecryptFailedException('Lost too many packets?')

            if self.decrypt_history[div[0]] == div[1]:
                raise DecryptFailedException('decrypt_iv in history')

        dst, tag = ocb_decrypt(self._aes, source[4:], bytes(div), len_plain)

        if tag[:3] != source[1:4]:
            raise DecryptFailedException('Tag did not match!')

        self.decrypt_history[div[0]] = div[1]

        if not late:
            self.decrypt_iv = div
        else:
            self.uiLate += 1

        self.uiGood += 1
        self.uiLost += lost

        self.tLastGood = time.perf_counter()

        return dst


def ocb_encrypt(aes, plain, nonce, *, insecure=False):
    delta = aes.encrypt(nonce)
    checksum = bytes(AES_BLOCK_SIZE)
    encrypted_blocks = []
    plain_block = b''

    pos = 0
    encrypted = bytearray(ceil(len(plain) / AES_BLOCK_SIZE) * AES_BLOCK_SIZE)
    while len(plain) - pos > AES_BLOCK_SIZE:
        plain_block = plain[pos:pos + AES_BLOCK_SIZE]
        delta = S2(delta)
        encrypted_block = xor(delta, aes.encrypt(xor(delta, plain_block)))
        checksum = xor(checksum, plain_block)

        encrypted[pos:pos + AES_BLOCK_SIZE] = encrypted_block
        pos += AES_BLOCK_SIZE

    # Counter-cryptanalysis described in section 9 of https://eprint.iacr.org/2019/311
    # For an attack, the second to last block (i.e. the last iteration of this loop)
    # must be all 0 except for the last byte (which may be 0 - 128).
    if not insecure and bytes(plain_block[:-1]) == bytes(AES_BLOCK_SIZE - 1):
        raise EncryptFailedException('Insecure input block: ' +
                                     'see section 9 of https://eprint.iacr.org/2019/311')

    len_remaining = len(plain) - pos
    delta = S2(delta)
    pad_in = struct.pack('>QQ', 0, len_remaining * 8)
    pad = aes.encrypt(xor(pad_in, delta))
    plain_block = plain[pos:] + pad[len_remaining - AES_BLOCK_SIZE:]

    checksum = xor(checksum, plain_block)
    encrypted_block = xor(pad, plain_block)
    encrypted[pos:] = encrypted_block

    delta = xor(delta, S2(delta))
    tag = aes.encrypt(xor(delta, checksum))

    return encrypted, tag


def ocb_decrypt(aes, encrypted, nonce, len_plain, *, insecure=False):
    delta = aes.encrypt(nonce)
    checksum = bytes(AES_BLOCK_SIZE)
    plain = bytearray(len_plain)

    pos = 0
    while len_plain - pos > AES_BLOCK_SIZE:
        encrypted_block = encrypted[pos:pos + AES_BLOCK_SIZE]
        delta = S2(delta)
        tmp = aes.decrypt(xor(delta, encrypted_block))
        plain_block = xor(delta, tmp)
        checksum = xor(checksum, plain_block)

        plain[pos:pos + AES_BLOCK_SIZE] = plain_block
        pos += AES_BLOCK_SIZE

    len_remaining = len_plain - pos
    delta = S2(delta)
    pad_in = struct.pack('>QQ', 0, len_remaining * 8)
    pad = aes.encrypt(xor(pad_in, delta))
    encrypted_zeropad = encrypted[pos:] + bytes(AES_BLOCK_SIZE - len_remaining)
    plain_block = xor(encrypted_zeropad, pad)

    checksum = xor(checksum, plain_block)
    plain[pos:] = plain_block[:len_remaining]

    # Counter-cryptanalysis described in section 9 of https://eprint.iacr.org/2019/311
    # In an attack, the decrypted last block would need to equal `delta ^ len(128)`.
    # With a bit of luck (or many packets), smaller values than 128 (i.e. non-full blocks) are also
    # feasible, so we check `plain_block` instead of `plain`.
    # Since our `len` only ever modifies the last byte, we simply check all remaining ones.
    if not insecure and plain_block[:-1] == delta[:-1]:
        raise DecryptFailedException('Possibly tampered/able block, discarding.')

    delta = xor(delta, S2(delta))
    tag = aes.encrypt(xor(delta, checksum))
    return plain, tag


def increment_iv(iv: bytearray, start: int = 0) -> bytearray:
    for i in range(start, AES_BLOCK_SIZE):
        iv[i] = (iv[i] + 1) % 0x100
        if iv[i] != 0:
            break
    return iv


def decrement_iv(iv: bytearray, start: int = 0) -> bytearray:
    for i in range(start, AES_BLOCK_SIZE):
        iv[i] = (iv[i] - 1) % 0x100
        if iv[i] != 0xFF:
            break
    return iv


def xor(a: bytes, b: bytes) -> bytes:
    return bytes(aa ^ bb for aa, bb in zip(a, b))


def S2(block: bytes) -> bytes:
    ll, uu = struct.unpack('>QQ', block)
    carry = ll >> 63
    block = struct.pack('>QQ',
                        ((ll << 1) | (uu >> 63)) & MAX64,
                        ((uu << 1) ^ (carry * 0x87)) & MAX64)
    return block

