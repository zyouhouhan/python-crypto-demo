import streamlit as st
import secrets
import time
from math import gcd
import io # ダウンロード機能のために追加

# ==========================================
# 1. RSA アルゴリズムの実装 (変更なし)
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

# ステータス表示(D)のために、内部で分割して呼び出せるよう構造を維持しつつ定義
def generate_rsa_keypair_steps(bits=1024, status_callback=None):
    if status_callback: status_callback("素数 p を生成中...")
    p = generate_prime(bits // 2)
    
    if status_callback: status_callback("素数 q を生成中...")
    q = generate_prime(bits // 2)
    
    if status_callback: status_callback("鍵 (e, d, n) を計算中...")
    n = p * q
    phi = (p - 1) * (q - 1)
    e = 65537
    while gcd(e, phi) != 1:
        e = secrets.randbelow(phi - 3) + 3
        if e % 2 == 0:
            e += 1
    d = modinv(e, phi)
    return ((e, n), (d, n))

# 互換性のためのラッパー
def generate_rsa_keypair(bits=1024):
    return generate_rsa_keypair_steps(bits)

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

# ==========================================
# 2. AES アルゴリズムの実装 (変更なし)
# ==========================================

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
# 3. Streamlit UI の実装
# ==========================================

st.set_page_config(page_title="Classic Crypto Demo", page_icon="🔐", layout="wide") # レイアウトをWideに変更

st.title("🔐 Pure Python Crypto Demo")

# 説明文（アコーディオン形式）
with st.expander("ℹ️ 暗号技術の詳しい解説を読む（クリックして展開）"):
    st.markdown("""
    Pythonのみで（ライブラリに頼らず）ゼロから実装した **RSA** と **AES** 暗号アルゴリズムのデモアプリです。
    内部の数学的処理やビット操作をコードで完全に再現しています。
    
    ### 機能について
    - **RSA**: 巨大な素数を使った公開鍵暗号。鍵の生成から体験できます。
    - **AES**: SPN構造を持つ共通鍵暗号。現在はECBモードで動作します。
    """)

# セッション状態の初期化
if 'rsa_keys' not in st.session_state: st.session_state['rsa_keys'] = None
if 'aes_key' not in st.session_state: st.session_state['aes_key'] = None
if 'rsa_cipher' not in st.session_state: st.session_state['rsa_cipher'] = None
if 'aes_cipher' not in st.session_state: st.session_state['aes_cipher'] = None

# 【A. サイドバーの実装】設定項目をサイドバーへ移動
with st.sidebar:
    st.header("⚙️ Settings (設定)")
    
    st.subheader("🔑 RSA Settings")
    rsa_bits = st.selectbox("RSA Key Size (Bits)", [512, 1024, 2048], index=1, help="鍵長が大きいほど安全ですが、生成と暗号化に時間がかかります。")
    
    # 【D. ステータス表示の強化】鍵生成ボタンとステータス表示
    if st.button("Generate RSA Keys (鍵生成)"):
        # st.statusを使って処理状況を可視化
        with st.status("RSA鍵ペアを生成中...", expanded=True) as status:
            start_time = time.time()
            
            # ステータス更新用のコールバック関数
            def update_status(msg):
                st.write(f"🔄 {msg}")
                time.sleep(0.1) # 視覚的にわかりやすくするためのウェイト
            
            # 鍵生成実行
            st.session_state['rsa_keys'] = generate_rsa_keypair_steps(rsa_bits, update_status)
            
            elapsed = time.time() - start_time
            status.update(label=f"鍵生成完了! ({elapsed:.3f}秒)", state="complete", expanded=False)

    st.divider()

    st.subheader("🛡️ AES Settings")
    aes_bits = st.selectbox("AES Key Size (Bits)", [128, 192, 256], index=0)
    
    col_k1, col_k2 = st.columns([3, 1])
    with col_k1:
        # 現在のAES鍵を表示・入力
        current_aes_hex = st.session_state['aes_key'].hex() if st.session_state['aes_key'] else ""
        key_input = st.text_input("AES Key (Hex)", value=current_aes_hex)
    with col_k2:
        st.write("")
        st.write("")
        if st.button("🎲", help="ランダムな鍵を生成"):
            st.session_state['aes_key'] = secrets.token_bytes(aes_bits // 8)
            st.rerun()

    # 鍵入力のバリデーション
    if key_input and key_input != current_aes_hex:
        try:
            b_key = bytes.fromhex(key_input)
            if len(b_key) != aes_bits // 8:
                st.error(f"長さ不一致: {len(b_key)}バイト (必要: {aes_bits//8}バイト)")
            else:
                st.session_state['aes_key'] = b_key
        except:
            st.error("無効なHex文字列")


tab_rsa, tab_aes = st.tabs(["🔑 RSA (公開鍵暗号)", "🛡️ AES (共通鍵暗号)"])

# --- RSA タブ ---
with tab_rsa:
    st.subheader("RSA Encryption / Decryption")
    
    # 鍵情報の表示とダウンロード
    if st.session_state['rsa_keys']:
        pub, priv = st.session_state['rsa_keys']
        e, n = pub
        d, _ = priv
        
        with st.expander("現在の鍵情報 (Public & Private Keys)"):
            st.code(f"Public Key (e, n):\ne = {e}\nn = {n}")
            st.code(f"Private Key (d, n):\nd = {d}\nn = {n}")
            
            # 【C. ダウンロード機能】鍵のダウンロード
            key_info_txt = f"RSA {rsa_bits} bit Keys\n\n[Public Key]\ne={e}\nn={n}\n\n[Private Key]\nd={d}\nn={n}"
            st.download_button("鍵情報をダウンロード (.txt)", key_info_txt, file_name="rsa_keys.txt")
    else:
        st.info("👈 サイドバーの「Generate RSA Keys」ボタンを押して鍵を作ってください。")

    st.divider()

    # 【B. 2カラムレイアウトの徹底】
    col_enc, col_dec = st.columns(2, gap="large")

    # --- 左カラム：暗号化 ---
    with col_enc:
        st.markdown("#### 1. Encrypt (暗号化)")
        rsa_msg = st.text_area("Plaintext (平文)", "Hello, RSA World!", height=150)
        
        if st.button("🔒 暗号化を実行"):
            if not st.session_state['rsa_keys']:
                st.error("鍵がありません。サイドバーで生成してください。")
            elif not rsa_msg:
                st.warning("メッセージを入力してください")
            else:
                try:
                    with st.spinner("暗号化計算中..."):
                        pub, _ = st.session_state['rsa_keys']
                        # 暗号化実行
                        encrypted_ints = rsa_encrypt(pub, rsa_msg)
                        st.session_state['rsa_cipher'] = encrypted_ints
                    st.success("暗号化成功！")
                except ValueError as ve:
                    st.error(f"エラー: {ve}")

    # --- 右カラム：復号と結果表示 ---
    with col_dec:
        st.markdown("#### 2. Decrypt (復号 & 結果)")
        
        if st.session_state['rsa_cipher']:
            # 暗号文のHex表示
            cipher_hex = "".join([f"{x:x}" for x in st.session_state['rsa_cipher']])
            st.text_area("Ciphertext (Hex)", cipher_hex, height=100, disabled=True)
            
            # 【C. ダウンロード機能】暗号文のダウンロード
            st.download_button("暗号文をダウンロード (.txt)", cipher_hex, file_name="rsa_ciphertext.txt")
            
            st.write("🔽")
            
            if st.button("🔓 復号を実行"):
                if not st.session_state['rsa_keys']:
                    st.error("鍵がありません")
                else:
                    _, priv = st.session_state['rsa_keys']
                    with st.spinner("復号計算中..."):
                        decrypted_text = rsa_decrypt(priv, st.session_state['rsa_cipher'])
                    
                    if decrypted_text:
                        st.success(f"復号結果:\n{decrypted_text}")
                    else:
                        st.error("復号失敗")
        else:
            st.info("暗号化を実行すると、ここに結果が表示されます。")

# --- AES タブ ---
with tab_aes:
    st.subheader("AES Encryption / Decryption (ECB Mode)")

    if not st.session_state['aes_key']:
        st.info("👈 サイドバーでAES鍵を設定・生成してください。")
    
    st.divider()

    # 【B. 2カラムレイアウトの徹底】
    col_a_enc, col_a_dec = st.columns(2, gap="large")

    aes = AES(aes_bits)

    # --- 左カラム：暗号化 ---
    with col_a_enc:
        st.markdown("#### 1. Encrypt (暗号化)")
        aes_msg = st.text_area("Plaintext (平文)", "Hello, AES World!", height=150, key="aes_input")
        
        if st.button("🔒 AES暗号化を実行"):
            if not st.session_state['aes_key']:
                st.error("鍵がセットされていません")
            elif not aes_msg:
                st.warning("メッセージを入力してください")
            else:
                try:
                    # 鍵スケジュール
                    expanded_key = aes.key_expansion(st.session_state['aes_key'])
                    # パディング & 暗号化
                    raw_bytes = aes_msg.encode('utf-8')
                    padded = pkcs7_pad(raw_bytes)
                    
                    out = bytearray()
                    for i in range(0, len(padded), 16):
                        block = list(padded[i:i+16])
                        enc_block = aes.encrypt_block(block, expanded_key)
                        out.extend(bytes(enc_block))
                    
                    st.session_state['aes_cipher'] = bytes(out)
                    st.success("暗号化成功！")
                except Exception as e:
                    st.error(f"エラー: {e}")

    # --- 右カラム：復号と結果表示 ---
    with col_a_dec:
        st.markdown("#### 2. Decrypt (復号 & 結果)")
        
        if st.session_state['aes_cipher']:
            cipher_bytes = st.session_state['aes_cipher']
            st.text_area("Ciphertext (Hex)", cipher_bytes.hex(), height=100, disabled=True)
            
            # 【C. ダウンロード機能】暗号文(Hex)のダウンロード
            st.download_button("暗号文をダウンロード (.txt)", cipher_bytes.hex(), file_name="aes_ciphertext.txt")

            st.write("🔽")

            if st.button("🔓 AES復号を実行"):
                if not st.session_state['aes_key']:
                    st.error("鍵がありません")
                else:
                    try:
                        expanded_key = aes.key_expansion(st.session_state['aes_key'])
                        out = bytearray()
                        for i in range(0, len(cipher_bytes), 16):
                            block = list(cipher_bytes[i:i+16])
                            dec_block = aes.decrypt_block(block, expanded_key)
                            out.extend(bytes(dec_block))
                        
                        unpadded = pkcs7_unpad(out)
                        dec_str = unpadded.decode('utf-8')
                        st.success(f"復号結果:\n{dec_str}")
                    except Exception as e:
                        st.error(f"復号失敗: {e}")
        else:
            st.info("暗号化を実行すると、ここに結果が表示されます。")
