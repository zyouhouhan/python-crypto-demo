import streamlit as st
import secrets
import time
import math
from datetime import datetime
from math import gcd

# ==========================================
# 1. RSA/AES アルゴリズムの実装 (既存機能)
# ==========================================

def is_prime(n, k=45):
    if n <= 1: return False
    if n <= 3: return True
    if n % 2 == 0: return False
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    for _ in range(k):
        a = secrets.randbelow(n - 3) + 2
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True

def generate_prime(bits):
    while True:
        p = secrets.randbits(bits)
        p |= (1 << bits - 1) | 1
        if is_prime(p):
            return p

def extended_gcd(a, b):
    if a == 0:
        return (b, 0, 1)
    else:
        g, y, x = extended_gcd(b % a, a)
        return (g, x - (b // a) * y, y)

def modinv(a, m):
    g, x, y = extended_gcd(a, m)
    if g != 1:
        raise Exception('modular inverse does not exist')
    return x % m

def generate_rsa_keypair(bits=1024):
    p = generate_prime(bits // 2)
    q = generate_prime(bits // 2)
    n = p * q
    phi = (p - 1) * (q - 1)
    e = 65537
    while gcd(e, phi) != 1:
        e = secrets.randbelow(phi - 3) + 3
        if e % 2 == 0:
            e += 1
    d = modinv(e, phi)
    return ((e, n), (d, n))

# PKCS#1 v1.5 padding
def pkcs1_v1_5_pad(data: bytes, block_size: int) -> bytes:
    if len(data) > block_size - 11:
        raise ValueError("データが長すぎます。鍵長を大きくするか、文を短くしてください。")
    padding_len = block_size - len(data) - 3
    padding = b''
    while len(padding) < padding_len:
        b_ = secrets.token_bytes(1)
        if b_ != b'\x00':
            padding += b_
    return b'\x00\x02' + padding + b'\x00' + data

def pkcs1_v1_5_unpad(data: bytes) -> bytes:
    if len(data) < 11 or data[0:2] != b'\x00\x02':
        raise ValueError("パディング形式エラー")
    sep_idx = data.find(b'\x00', 2)
    if sep_idx < 0:
        raise ValueError("パディング区切りが見つかりません")
    return data[sep_idx+1:]

def rsa_encrypt(pk, plaintext):
    key, n = pk
    k = (n.bit_length() + 7) // 8
    data = plaintext.encode('utf-8')
    max_block_size = k - 11
    encrypted_blocks = []
    for i in range(0, len(data), max_block_size):
        block = data[i:i+max_block_size]
        padded = pkcs1_v1_5_pad(block, k)
        m = int.from_bytes(padded, 'big')
        c = pow(m, key, n)
        encrypted_blocks.append(c)
    return encrypted_blocks

def rsa_decrypt(pk, ciphertext_blocks):
    key, n = pk
    k = (n.bit_length() + 7) // 8
    decrypted_blocks = []
    for c in ciphertext_blocks:
        m = pow(c, key, n)
        padded = m.to_bytes(k, 'big')
        try:
            data = pkcs1_v1_5_unpad(padded)
            decrypted_blocks.append(data)
        except ValueError:
            return None
    return b''.join(decrypted_blocks).decode('utf-8', errors='ignore')


# AESの実装
SBOX = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
]

INV_SBOX = [
    0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
    0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
    0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
    0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
    0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
    0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
    0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
    0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
    0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
    0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
    0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
    0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
    0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
    0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
    0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d
]

class AES:
    def __init__(self, key_size=128):
        self.key_size = key_size
        self.nb = 4
        self.nk = key_size // 32
        self.nr = {128: 10, 192: 12, 256: 14}[key_size]

    def sub_bytes(self, state):
        for i in range(4):
            for j in range(4):
                state[i][j] = SBOX[state[i][j]]
        return state

    def inv_sub_bytes(self, state):
        for i in range(4):
            for j in range(4):
                state[i][j] = INV_SBOX[state[i][j]]
        return state

    def shift_rows(self, state):
        state[1] = state[1][1:] + state[1][:1]
        state[2] = state[2][2:] + state[2][:2]
        state[3] = state[3][3:] + state[3][:3]
        return state

    def inv_shift_rows(self, state):
        state[1] = state[1][-1:] + state[1][:-1]
        state[2] = state[2][-2:] + state[2][:-2]
        state[3] = state[3][-3:] + state[3][:-3]
        return state

    def mix_columns(self, state):
        def gmul(a, b):
            p = 0
            for _ in range(8):
                if b & 1: p ^= a
                hi_bit_set = a & 0x80
                a <<= 1
                if hi_bit_set: a ^= 0x1b
                a &= 0xff
                b >>= 1
            return p
        for i in range(4):
            s0, s1, s2, s3 = state[0][i], state[1][i], state[2][i], state[3][i]
            state[0][i] = gmul(0x02, s0) ^ gmul(0x03, s1) ^ s2 ^ s3
            state[1][i] = s0 ^ gmul(0x02, s1) ^ gmul(0x03, s2) ^ s3
            state[2][i] = s0 ^ s1 ^ gmul(0x02, s2) ^ gmul(0x03, s3)
            state[3][i] = gmul(0x03, s0) ^ s1 ^ s2 ^ gmul(0x02, s3)
        return state

    def inv_mix_columns(self, state):
        def gmul(a, b):
            p = 0
            for _ in range(8):
                if b & 1: p ^= a
                hi_bit_set = a & 0x80
                a <<= 1
                if hi_bit_set: a ^= 0x1b
                a &= 0xff
                b >>= 1
            return p
        for i in range(4):
            s0, s1, s2, s3 = state[0][i], state[1][i], state[2][i], state[3][i]
            state[0][i] = gmul(0x0e, s0) ^ gmul(0x0b, s1) ^ gmul(0x0d, s2) ^ gmul(0x09, s3)
            state[1][i] = gmul(0x09, s0) ^ gmul(0x0e, s1) ^ gmul(0x0b, s2) ^ gmul(0x0d, s3)
            state[2][i] = gmul(0x0d, s0) ^ gmul(0x09, s1) ^ gmul(0x0e, s2) ^ gmul(0x0b, s3)
            state[3][i] = gmul(0x0b, s0) ^ gmul(0x0d, s1) ^ gmul(0x09, s2) ^ gmul(0x0e, s3)
        return state

    def add_round_key(self, state, round_key):
        for i in range(4):
            for j in range(4):
                state[i][j] ^= round_key[i][j]
        return state

    def key_expansion(self, key):
        def sub_word(word): return [SBOX[b] for b in word]
        def rot_word(word): return word[1:] + word[:1]
        def rcon(i):
            r = 1
            for _ in range(i - 1):
                r = ((r << 1) ^ 0x1b) & 0xff if r & 0x80 else r << 1
            return [r, 0, 0, 0]

        key_words = [key[i:i + 4] for i in range(0, len(key), 4)]
        expanded_key = key_words[:]
        for i in range(self.nk, self.nb * (self.nr + 1)):
            temp = expanded_key[i - 1][:]
            if i % self.nk == 0:
                temp = [a ^ b for a, b in zip(sub_word(rot_word(temp)), rcon(i // self.nk))]
            elif self.nk > 6 and i % self.nk == 4:
                temp = sub_word(temp)
            expanded_key.append([a ^ b for a, b in zip(expanded_key[i - self.nk], temp)])
        return expanded_key

    def encrypt_block(self, block, expanded_key):
        state = [[block[i + 4*j] for j in range(4)] for i in range(4)]
        round_key = [[expanded_key[j][i] for j in range(4)] for i in range(4)]
        state = self.add_round_key(state, round_key)
        for rnd in range(1, self.nr):
            state = self.sub_bytes(state)
            state = self.shift_rows(state)
            state = self.mix_columns(state)
            round_key = [[expanded_key[4*rnd + j][i] for j in range(4)] for i in range(4)]
            state = self.add_round_key(state, round_key)
        state = self.sub_bytes(state)
        state = self.shift_rows(state)
        round_key = [[expanded_key[4*self.nr + j][i] for j in range(4)] for i in range(4)]
        state = self.add_round_key(state, round_key)
        return [state[i][j] for j in range(4) for i in range(4)]

    def decrypt_block(self, block, expanded_key):
        state = [[block[i + 4*j] for j in range(4)] for i in range(4)]
        round_key = [[expanded_key[4*self.nr + j][i] for j in range(4)] for i in range(4)]
        state = self.add_round_key(state, round_key)
        for rnd in range(self.nr-1, 0, -1):
            state = self.inv_shift_rows(state)
            state = self.inv_sub_bytes(state)
            round_key = [[expanded_key[4*rnd + j][i] for j in range(4)] for i in range(4)]
            state = self.add_round_key(state, round_key)
            state = self.inv_mix_columns(state)
        state = self.inv_shift_rows(state)
        state = self.inv_sub_bytes(state)
        round_key = [[expanded_key[j][i] for j in range(4)] for i in range(4)]
        state = self.add_round_key(state, round_key)
        return [state[i][j] for j in range(4) for i in range(4)]

def pkcs7_pad(data: bytes, block_size: int = 16) -> bytes:
    pad_len = block_size - (len(data) % block_size)
    if pad_len == 0: pad_len = block_size
    return data + bytes([pad_len]) * pad_len

def pkcs7_unpad(data: bytes) -> bytes:
    if len(data) == 0: raise ValueError('空データ')
    pad_len = data[-1]
    if pad_len < 1 or pad_len > 16: raise ValueError('パディング異常')
    if data[-pad_len:] != bytes([pad_len]) * pad_len: raise ValueError('パディング不一致')
    return data[:-pad_len]

# ==========================================
# 2. 脆弱性デモ用の追加機能 (New Functions)
# ==========================================

def elapsed_ms(start, end=None):
    if end is None:
        end = datetime.now()
    return (end - start).total_seconds() * 1000.0

def generate_prime_weak(bits: int) -> int:
    """脆弱性デモ用にビット数を厳密に守る素数生成"""
    assert bits >= 2
    while True:
        p = secrets.randbits(bits)
        p |= (1 << (bits - 1)) | 1
        if is_prime(p):
            return p

def generate_weak_keypair(bits: int):
    """脆弱性デモ用の鍵生成関数"""
    start = datetime.now()
    half = max(2, bits // 2)

    p = generate_prime_weak(half)
    q = generate_prime_weak(half)
    while p == q:
        q = generate_prime_weak(half)

    n = p * q
    phi = (p - 1) * (q - 1)
    e = 65537

    if math.gcd(e, phi) != 1:
        # 作り直し
        p = generate_prime_weak(half)
        q = generate_prime_weak(half)
        while p == q:
            q = generate_prime_weak(half)
        n = p * q
        phi = (p - 1) * (q - 1)

    d = modinv(e, phi)
    gen_ms = elapsed_ms(start)
    return (e, n), (d, n), p, q, phi, gen_ms

def factorize_trial(n: int):
    """試し割りによる素因数分解"""
    start = datetime.now()
    if n % 2 == 0:
        p, q = 2, n // 2
        return (p, q), elapsed_ms(start)

    r = int(math.isqrt(n))
    for i in range(3, r + 1, 2):
        if n % i == 0:
            p, q = i, n // i
            return (p, q), elapsed_ms(start)
    return (None, None), elapsed_ms(start)

def brute_force_d(e: int, phi: int):
    """秘密鍵dの総当たり探索"""
    start = datetime.now()
    # デモ用：phiが大きすぎると終わらないので安全装置
    if phi > 10_000_000_000_000:
        return None, elapsed_ms(start)
        
    for d in range(1, phi):
        if (d * e) % phi == 1:
            return d, elapsed_ms(start)
    return None, elapsed_ms(start)

def attack_from_public_key(e: int, n: int):
    """完全攻撃シナリオ実行"""
    attack_start = datetime.now()

    # 1) 因数分解
    (p, q), factor_ms = factorize_trial(n)
    if p is None or q is None:
        total_ms = elapsed_ms(attack_start)
        return {"success": False, "reason": "因数分解失敗", "factor_ms": factor_ms, "total_ms": total_ms}

    # 2) φ(n)
    phi_start = datetime.now()
    phi = (p - 1) * (q - 1)
    phi_ms = elapsed_ms(phi_start)

    # 3) 秘密鍵d 総当たり
    d, brute_ms = brute_force_d(e, phi)

    total_ms = elapsed_ms(attack_start)
    return {
        "success": d is not None,
        "p": p, "q": q, "phi": phi, "d": d,
        "factor_ms": factor_ms, "phi_ms": phi_ms, "brute_ms": brute_ms,
        "total_ms": total_ms,
    }

# ==========================================
# 3. Streamlit UI の実装
# ==========================================

st.set_page_config(page_title="Classic Crypto Demo", page_icon="🔐", layout="centered")

with st.sidebar:
    try:
        st.image("icon.jpeg", width=150)
    except:
        pass

st.title("🔐 Pure Python Crypto Demo")

# --- 解説部分（3分割） ---

with st.expander("ℹ️ 解説1：暗号の基本とシーザー暗号"):
    st.markdown("""
●暗号について

　暗号とは、発信者と受信者以外の誰にも知られないように情報を受け渡すための技術です。

　シーザー暗号を例に挙げましょう。紀元前1世紀ごろにローマ帝国を支配したジュリアス・シーザーが使用したことからこの名前がつけられています。この暗号の仕組みはとても単純です。アルファベットの文章において、その各文字をアルファベット順に何文字かずらすのです。 """)

    try:
        st.image("caesar_diagram.png", caption="シーザー暗号の仕組み（例：3文字ずらし）", use_container_width=True)
    except:
        pass

    st.markdown("""
このような文章をシーザー暗号を用いて暗号化するとしましょう。3文字ずらすことにします。

There was a table set out under a tree in front of the house and the march hare and the hatter were having tea at it.

これがアルファベット順です。

ABCDEFGHIJKLMNOPQRSTUVWXYZ

この暗号化の答えは、次のようになります。

Wkhuh zdv d wdeoh vhw rxw xqghu d wuhh lq iurqw ri wkh krxvh dqg wkh pdufk kduh dqg wkh kdwwhu zhuh kdylqj whd dw lw.

この暗号文は、第三者からすると意味不明なアルファベットの羅列にしか見えません。しかし受信者からすれば、この文章のアルファベット順を3つ逆にずらすだけ（平文に戻す動作を復号と呼びます）で、元の文が手に入ります。発信者と受信者以外には知られないように情報を受け渡すとは、こういったことです。

では、もし第三者がこの暗号文を解読するとしたら、どういった方法を使えばよいでしょうか。

結論は、「この文章は、平文をアルファベット順に3つずらした暗号だ」ということが分かればこの暗号文を簡単に解読できます。逆にいうと、発信者と受信者はこの情報を絶対に秘密にしなくてはなりません。こういった暗号化のルールを鍵と呼びます。

また、暗号文をよく観察すると、「wkh」というのがよく出てくることに気づくかと思います。

これをもし仮に英語の「the」だと仮定すると、最初の「Wkhuh」は「Theue」…？というように、シーザー暗号は暗号文だけを考えてもかなり解読できてしまうので、暗号としてはとても弱く、実用に適さないものです。こういった暗号の仕組み自体の弱点を暗号の脆弱性（ぜいじゃくせい）と呼びます。

こうしてみると、暗号を実用的なものにするためには、①鍵を絶対に第三者にバレないようにすること、②暗号文から平文を推測されないようにすること、という二つの条件が必要であることがわかります。 """)

    try:
        st.image("caesar_vulnerability.jpg", caption="図解：暗号の脆弱性と対策", use_container_width=True)
    except:
        pass


with st.expander("ℹ️ 解説2：RSA暗号（公開鍵暗号）"):
    st.markdown("""
●RSA暗号について
　RSA暗号は、暗号の一つです。1977年に開発され、現在に至るまでインターネット通信の暗号化など広く用いられています。この暗号の特徴は、公開鍵暗号方式というシステムを採用したことです。
　シーザー暗号では、発信者も受信者も「３」という鍵を双方で共有し暗号化と復号を行っていました。これを「共通鍵暗号方式」と呼びます。しかし、この方式では、受信者は発信者から鍵を受け取らなくては復号ができません。その受け渡す過程で、鍵を第三者に盗み取られてしまうかもしれないという危険性があります。
　この危険性へ対処できるのが公開鍵暗号方式です。この方式による暗号化では、まず受信者が、暗号化を行う公開鍵と、復号を行う秘密鍵との２つの鍵を作ります。そして公開鍵を発信者に送り、発信者は公開鍵で平文を暗号化します。こうして、発信者からの暗号文を受信者が秘密鍵で復号します。この場合、受信者が秘密鍵を保持しておけば、第三者から鍵を奪われることはありません。
　それでは、どのようにして公開鍵と秘密鍵を関連付け、しかも秘密鍵を知られないようにするのでしょうか。RSA暗号では、整数の素因数分解を用いて実装しています。例えば1765117147=41771×42257という素因数分解を計算することはとても困難です。2.3.5…と素数で次々に割って計算していくと、41771に辿り着くまでには長い時間がかかります。逆に、41771×42257=1765117147という計算は、簡単に行うことができます。
　このことを用いて、RSA暗号では、二つの異なる素数を秘密鍵、その積が公開鍵と結びつくような仕組みを作り、暗号化と復号を行うことで、鍵の安全性を保っています。ちなみに、現在RSA暗号のとして実用されている公開鍵となる素数の大きさは、ゆうに2の2048乗（約600桁）以上です。
　なお、公開鍵暗号方式は、鍵の生成や公開鍵と秘密鍵を結びつける作業に合同式やユークリッドの互除法などの複雑な計算を利用するので、共通鍵暗号方式よりも処理が遅くなってしまう欠点があります。なので、音声や映像などの、次々に送られてくるデータを高速で暗号化しなくてはならない場面では、鍵の共有には公開鍵暗号を用いて、それらの鍵で共通鍵暗号による暗号化を行うことが多いです。
""")

    try:
        st.image("rsa_description.jpg", caption="図解：RSA暗号における公開鍵と秘密鍵の役割", use_container_width=True)
    except:
        st.error("画像(rsa_description.jpg)が見つかりません")


with st.expander("ℹ️ 解説3：AES暗号（共通鍵暗号）"):
    # 注: 以下のテキストは提供されたものをそのまま使用していますが、AESは一般に「共通鍵暗号方式」です。
    st.markdown("""
●AES暗号について
　AES暗号は、代表的な公開鍵暗号方式です。2000年に開発され、その高い安全性や処理の早さが高い評価を得て、無線LAN通信の暗号化など、現在標準的に幅広く使用されています。
　AES暗号の特徴は、4つの段階によるラウンドを何度も繰り返すことによって、平文を混ぜ合わせることです。それらの段階は、平文の順列をずらしたり、表に従って置き換えたり、鍵と平文を混ぜ合わせたりすることで、平文と暗号文との結びつきを弱めています。こうした動作を何度も繰り返し、平文を推測されないようにするのです。RSA暗号の処理では素因数分解のため整数の演算を多く使いましたが、AES暗号はこのように単純な操作のみで暗号化できます。なので、RSA暗号よりも早くアルゴリズムを処理できるのです。
 """)
    try:
        st.image("aes_description.jpg", caption="図解：AES暗号の仕組み（4つの変換工程）", use_container_width=True)
    except:
        st.error("画像(aes_description.jpg)が見つかりません")

st.markdown("""
Pythonのみでゼロから実装した **RSA** と **AES** 暗号アルゴリズムのデモアプリです。
内部の数学的処理やビット操作をコードで完全に再現しています。
""")
st.divider()
# ==========================================
# スライド風タブメニュー（サイドバー切り替え）
# ==========================================

# 1. ページ状態の管理
if 'current_page' not in st.session_state:
    st.session_state['current_page'] = "RSA"

# 2. サイドバーをナビゲーションメニューにする
with st.sidebar:
    st.title("🛡️ Crypto Dashboard")
    st.markdown("---")
    
    # 各ボタン。クリックするとページ状態が更新される
    if st.button("🔑 RSA (公開鍵暗号)", use_container_width=True):
        st.session_state['current_page'] = "RSA"
    if st.button("🛡️ AES (共通鍵暗号)", use_container_width=True):
        st.session_state['current_page'] = "AES"
    if st.button("💥 脆弱性デモ", use_container_width=True):
        st.session_state['current_page'] = "Demo"


# ==========================================
# 3. メインコンテンツの表示切り替え
# ==========================================

#===================
# --- RSA ページ ---
#===================

if st.session_state['current_page'] == "RSA":
    st.header("🔑 RSA Encryption")
    st.info("素因数分解の困難性を利用した公開鍵暗号方式です。")
    st.subheader("STEP1: 鍵ペアを生成")
    if 'rsa_keys' not in st.session_state:
        st.session_state['rsa_keys'] = None

    col1, col2 = st.columns([2, 1])
    with col1:
        bits = st.selectbox("鍵のビット長 (大きいほど安全ですが遅くなります)", [512, 1024, 2048], index=1)
    with col2:
        st.write("")
    if st.button("鍵ペアを生成"):
            start_time = time.time()
            st.session_state['rsa_keys'] = generate_rsa_keypair(bits)
            g_elapsed = (time.time() - start_time) * 1000
            st.session_state['rsa_gen_time'] = g_elapsed
            st.success(f"鍵生成完了 ({g_elapsed/1000:.3f}秒)")

    if st.session_state['rsa_keys']:
        pub, priv = st.session_state['rsa_keys']
        e, n = pub
        d, _ = priv

        with st.expander("生成された鍵の詳細を見る", expanded=True):
            st.markdown(f"**Public Key (e, n):**")
            st.code(f"e = {e}\nn = {n}")
            st.markdown(f"**Private Key (d, n):**")
            st.code(f"d = {d}\nn = {n}")
    else:
        st.info("鍵のビット長を選択し、鍵ペアを生成してください。")
        
    st.divider()    
    st.subheader("STEP2: 暗号化/復号")
    rsa_msg = st.text_input("暗号化したいメッセージ (任意の文章を暗号化できます)", "Hello, RSA World!")
    col_enc, col_dec = st.columns(2)
    with col_enc:
        if st.button("暗号化 (Encrypt)"):
            # ここで「保存されている鍵」があるかチェックし、直接取り出す
            if st.session_state['rsa_keys'] and rsa_msg:
                # pub と priv をその場で取り出す
                pub_key, priv_key = st.session_state['rsa_keys']
                
                start_time = time.time()
                # 取り出した pub_key を使う
                st.session_state['rsa_cipher'] = rsa_encrypt(pub_key, rsa_msg)
                
                st.session_state['rsa_enc_time'] = (time.time() - start_time) * 1000
                
                # 前回の NameError 対策も合わせて修正（encrypted_ints を使わない）
                st.session_state['rsa_cipher_show'] = "".join([f"{x:x}" for x in st.session_state['rsa_cipher']])
            else:
                st.error("鍵が生成されていないか、メッセージが空です。")
                
        if 'rsa_cipher_show' in st.session_state:
            st.text_area("暗号文 (16進数表現)", st.session_state['rsa_cipher_show'], height=100)
            st.info("""
            この暗号文は、入力されている平文をRSA暗号を用いて暗号化したものです。
                
            この暗号文から第三者が平文を簡単に予測することは不可能です。
            """)
                
    with col_dec:
        if 'rsa_cipher' in st.session_state:
            if st.button("復号 (Decrypt)"):
                if 'rsa_cipher' in st.session_state:
                    start_time = time.time()
                    decrypted_text = rsa_decrypt(priv, st.session_state['rsa_cipher'])
                    st.session_state['rsa_dec_time'] = (time.time() - start_time) * 1000
                    st.session_state['rsa_decrypted'] = decrypted_text
    
    if 'rsa_decrypted' in st.session_state:
        st.success(f"復号された平文: {st.session_state['rsa_decrypted']}")
        
    st.divider()
    st.subheader("STEP3: イベント別計測結果")
    g_t = st.session_state.get('rsa_gen_time', 0.0)
    e_t = st.session_state.get('rsa_enc_time', 0.0)
    d_t = st.session_state.get('rsa_dec_time', 0.0)
    
    c1, c2, c3 = st.columns(3)
    c1.metric("鍵生成", f"{g_t:.2f} ms")
    c2.metric("暗号化", f"{e_t:.2f} ms")
    c3.metric("復号", f"{d_t:.2f} ms")

    st.divider()
    st.info(f"合計処理時間: **{g_t + e_t + d_t:.2f} ミリ秒**")
    
#===================
# --- AES ページ ---
#===================
elif st.session_state['current_page'] == "AES":
    st.header("🛡️ AES Encryption")
    st.info("SPN構造を持つ、現在標準的な共通鍵暗号方式です。")
    
    st.subheader("STEP1: 鍵を生成")
    if 'aes_key' not in st.session_state:
        st.session_state['aes_key'] = None
    
    aes_bits = st.selectbox("AES鍵長", [128, 192, 256])
    col_a1, col_a2 = st.columns([3, 1])
    with col_a1:
        key_input = st.text_input("秘密鍵 (Hex)", value="" if not st.session_state['aes_key'] else st.session_state['aes_key'].hex())
    with col_a2:
        st.write("")
        if st.button("ランダム鍵生成"):
            start_gen = time.time()
            st.session_state['aes_key'] = secrets.token_bytes(aes_bits // 8)
            st.session_state['aes_gen_time'] = (time.time() - start_gen) * 1000 # AES用の変数に保存
            
            # 新しい鍵を生成すると古い結果をリセットする
            if 'aes_cipher' in st.session_state: del st.session_state['aes_cipher']
            if 'aes_decrypted' in st.session_state: del st.session_state['aes_decrypted']
            st.session_state['aes_enc_time'] = 0.0
            st.session_state['aes_dec_time'] = 0.0
            st.rerun()
            
    if st.session_state['aes_key']:
        st.success(f"現在の鍵: {st.session_state['aes_key'].hex()}")
    else:
            st.info("鍵長を選択しランダム鍵生成をクリックしてください。")
        
    st.divider()
    st.subheader("STEP2: 暗号化/復号") 
    aes_msg = st.text_input("暗号化したいメッセージ (任意の文章を暗号化できます)", "Hello, AES World!")
        
    col_aes_enc, col_aes_dec = st.columns(2)
    aes_obj = AES(aes_bits)
    with col_aes_enc:
        if st.button("AES 暗号化"):
            if aes_msg:
                start_enc = time.time() # 計測開始
                expanded_key = aes_obj.key_expansion(st.session_state['aes_key'])
                padded = pkcs7_pad(aes_msg.encode('utf-8'))
                out = bytearray()
                for i in range(0, len(padded), 16):
                    block = list(padded[i:i+16])
                    enc_block = aes_obj.encrypt_block(block, expanded_key)
                    out.extend(bytes(enc_block))
                st.session_state['aes_cipher'] = bytes(out)
                st.session_state['aes_enc_time'] = (time.time() - start_enc) * 1000 # AES用の変数に保存
                
                if 'aes_cipher' in st.session_state:
                    st.code(st.session_state['aes_cipher'].hex(), language="text")
                    st.info("""
                        この暗号文は、入力されている平文をAES暗号を用いて暗号化したものです。
                        
                        この暗号文から第三者が平文を簡単に予測することは不可能です。
                        """)
                
    with col_aes_dec:
       if 'aes_cipher' in st.session_state:
            if st.button("AES 復号"):
                start_dec = time.time() # 計測開始
                expanded_key = aes_obj.key_expansion(st.session_state['aes_key'])
                cipher_data = st.session_state['aes_cipher']
                out = bytearray()
                for i in range(0, len(cipher_data), 16):
                    block = list(cipher_data[i:i+16])
                    dec_block = aes_obj.decrypt_block(block, expanded_key)
                    out.extend(bytes(dec_block))
                st.session_state['aes_decrypted'] = pkcs7_unpad(out).decode('utf-8')
                st.session_state['aes_dec_time'] = (time.time() - start_dec) * 1000 # AES用の変数に保存
    if 'aes_decrypted' in st.session_state:
                st.success(f"復号結果: {st.session_state['aes_decrypted']}")
            
    st.divider()
    st.subheader("STEP3: イベント別計測結果")
    ga_t = st.session_state.get('aes_gen_time', 0.0)
    ea_t = st.session_state.get('aes_enc_time', 0.0)
    da_t = st.session_state.get('aes_dec_time', 0.0)
    
    c1, c2, c3 = st.columns(3)
    c1.metric("鍵生成", f"{ga_t:.2f} ms")
    c2.metric("暗号化", f"{ea_t:.2f} ms")
    c3.metric("復号", f"{da_t:.2f} ms")
        
    st.divider()
    st.info(f"合計処理時間: **{ga_t + ea_t + da_t:.2f} ミリ秒**")

#=========================
# --- 脆弱性デモ ページ ---
#=========================

elif st.session_state['current_page'] == "Demo":
    st.header("💥 RSA完全攻撃デモ")
    st.warning("⚠️ 公開鍵から秘密鍵を特定する実験です。")

    if 'weak_keys' not in st.session_state:
        st.session_state['weak_keys'] = None

    weak_bits = st.number_input("RSA鍵長 (推奨: 16〜30)", min_value=8, max_value=32, value=16)
    if st.button("脆弱な鍵ペアを生成"):
        pub, priv, p, q, phi, gen_ms = generate_weak_keypair(weak_bits)
        st.session_state['weak_keys'] = {"pub": pub, "priv": priv, "p": p, "q": q, "phi": phi, "gen_ms": gen_ms}

    if st.session_state['weak_keys']:
        wk = st.session_state['weak_keys']
        e, n = wk['pub']
        st.info(f"公開鍵: e={e}, n={n}")
        #==プログレスバー==#
        if st.button("攻撃開始 (Attack!)", type="primary"):
            status_area = st.empty()
            
            # 1. 探索開始のメッセージを表示
            status_area.warning("🔍 秘密鍵を探索中... (素因数分解を実行中)")
            
            # 2. 純粋な計算時間を測る
            start_time = time.time()
            result = attack_from_public_key(e, n)
            total_ms = (time.time() - start_time) * 1000
            
            # 3. 計算が終わったらメッセージを消す
            status_area.empty()
            # 5. 結果を表示
            if result["success"]:
                st.success(f"🎉 解読成功！ 秘密鍵 d = {result['d']}")
                st.balloons()
            else:
                st.error("攻撃に失敗しました。")

























































































