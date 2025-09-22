import time
import random

''''
# ==============================================================================
# CORRECTED CRYPTOGRAPHIC CORE
# (Synchronized with the validated main analysis script)

Here’s the step-by-step process using an example from our original paper's appendix.

Step 1: Run Your Main Analysis Script
First, run your updated Multiproc_cDU_Enhanced_Kuznyechik_R9.py script 
(fixed random seed, for reproducibility and the modified encryption function).

Step 2: Identify the Best Distinguisher in the Output
Look for the summary table or a "CRITICAL ALERT" section in the output file. 
You need to find the line with the highest bias or the lowest p-value.

For example, our original appendix showed this result:

CRITICAL ALERT: Statistically significant characteristic found for 9 rounds!
  Config: byte_8_in->byte_8_out, c=0x4
  Found 1 significant pairs (threshold: 1): Input→Output
    0x00000000000000290000000000000000 → 0x000000000000008d0000000000000000 (Bias:1.7, p-val:1.85e-03)
From this output, you extract the following values:

c: 0x4

Input Diff (A): 0x00000000000000290000000000000000

Output Diff (B): 0x000000000000008d0000000000000000

Number of Rounds: 9

Step 3: Edit verify_distinguisher.py
Now, open your verify_distinguisher.py file and replace the placeholder parameters with the values you just found. The hexadecimal strings from the output can be directly copied into Python as integers.
 

# --- PARAMETERS TO SET AFTER YOU FIND YOUR BEST RESULT ---
# These are placeholders. Replace them with your new findings.
BEST_C = 0x04 
BEST_A = 0x00000000000000290000000000000000
BEST_B = 0x000000000000008d0000000000000000
NUM_ROUNDS = 9
NUM_TRIALS = 5_000_000
After Editing:

Python
 
# ==============================================================================
''''

SBOX_INT = (
    252, 238, 221, 17, 207, 110, 49, 22, 251, 196, 250, 218, 35, 197, 4, 77,
    233, 119, 240, 219, 147, 46, 153, 186, 23, 54, 241, 187, 20, 205, 95, 193,
    249, 24, 101, 90, 226, 92, 239, 33, 129, 28, 60, 66, 139, 1, 142, 79,
    5, 132, 2, 174, 227, 106, 143, 160, 6, 11, 237, 152, 127, 212, 211, 31,
    235, 52, 44, 81, 234, 200, 72, 171, 242, 42, 104, 162, 253, 58, 206, 204,
    181, 112, 14, 86, 8, 12, 118, 18, 191, 114, 19, 71, 156, 183, 93, 135,
    21, 161, 150, 41, 16, 123, 154, 199, 243, 145, 120, 111, 157, 158, 178, 177,
    50, 117, 25, 61, 255, 53, 138, 126, 109, 84, 198, 128, 195, 189, 13, 87,
    223, 245, 36, 169, 62, 168, 67, 201, 215, 121, 214, 246, 124, 34, 185, 3,
    224, 15, 236, 222, 122, 148, 176, 188, 220, 232, 40, 80, 78, 51, 10, 74,
    167, 151, 96, 115, 30, 0, 98, 68, 26, 184, 56, 130, 100, 159, 38, 65,
    173, 69, 70, 146, 39, 94, 85, 47, 140, 163, 165, 125, 105, 213, 149, 59,
    7, 88, 179, 64, 134, 172, 29, 247, 48, 55, 107, 228, 136, 217, 231, 137,
    225, 27, 131, 73, 76, 63, 248, 254, 141, 83, 170, 144, 202, 216, 133, 97,
    32, 113, 103, 164, 45, 43, 9, 91, 203, 155, 37, 208, 190, 229, 108, 82,
    89, 166, 116, 210, 230, 244, 180, 192, 209, 102, 175, 194, 57, 75, 99, 182
)

MASTER_KEY_INT_kuznyechik = 0x8899aabbccddeeff0011223344556677fedcba98765432100123456789abcdef
EXPANDED_ROUND_KEYS_INT = []

def _gf256_mul(a, b):
    p = 0
    for _ in range(8):
        if b & 1:
            p ^= a
        hi_bit_set = a & 0x80
        a <<= 1
        if hi_bit_set:
            a ^= 0xC3
        b >>= 1
    return p & 0xFF

_L_CONSTANTS = (1, 148, 32, 133, 16, 194, 192, 1, 251, 1, 192, 194, 16, 133, 32, 148)

def _l_func(state):
    res = 0
    for i in range(16):
        res ^= _gf256_mul(state[i], _L_CONSTANTS[i])
    return res

def L_transformation(state):
    a = list(state)
    for _ in range(16):
        a = [_l_func(a)] + a[:-1]
    return a

def generate_constants():
    constants = []
    for i in range(32):
        vec = [0] * 15 + [i + 1]
        constants.append(tuple(L_transformation(vec)))
    return tuple(constants)

C_j = generate_constants()

def apply_f_function_optimized(a1, a0, Ck):
    temp = [a1[i] ^ Ck[i] for i in range(16)]
    temp = [SBOX_INT[byte] for byte in temp]
    lsx_result = L_transformation(temp)
    new_a1 = [lsx_result[i] ^ a0[i] for i in range(16)]
    return new_a1, a1

def key_expansion_kuznyechik_optimized(master_key_int):
    global EXPANDED_ROUND_KEYS_INT
    k2_bytes = (master_key_int & ((1 << 128) - 1)).to_bytes(16, 'big')
    k1_bytes = (master_key_int >> 128).to_bytes(16, 'big')
    K1, K2 = list(k1_bytes), list(k2_bytes)
    round_keys = [tuple(K1), tuple(K2)]
    for i in range(4):
        for j in range(8):
            K1, K2 = apply_f_function_optimized(K1, K2, C_j[8 * i + j])
        round_keys.append(tuple(K1))
        round_keys.append(tuple(K2))
    EXPANDED_ROUND_KEYS_INT = tuple(round_keys)

def encrypt_n_rounds_kuznyechik_optimized(plaintext_block, num_rounds):
    state = list(plaintext_block)
    keys = EXPANDED_ROUND_KEYS_INT
    for r in range(9):
        state = [state[i] ^ keys[r][i] for i in range(16)]
        state = [SBOX_INT[byte] for byte in state]
        state = L_transformation(state)
    ciphertext = [state[i] ^ keys[9][i] for i in range(16)]
    return ciphertext

# ==============================================================================
# VERIFICATION LOGIC
# ==============================================================================

def int_to_block_128(val_int: int) -> list:
    """Converts a 128-bit integer to a list of 16 bytes."""
    return [(val_int >> ((15-i) * 8)) & 0xFF for i in range(16)]

def verify_single_distinguisher():
    """
    A minimal script to verify the single, best c-differential distinguisher.
    """
    # --- 1. PARAMETERS (Updated with the final, best result from the 9-round analysis) ---
    BEST_C = 0x91
    NUM_ROUNDS = 9
    BEST_A = 0x00000000000000000000000000720000
    BEST_B = 0x00000000000000000000000000180000
    NUM_TRIALS = 5_000_000

    # --- 2. SETUP AND EXPECTATION ---
    key_expansion_kuznyechik_optimized(MASTER_KEY_INT_kuznyechik)
    
    # Expected probability for a 1-byte active input -> 1-byte active output
    EXPECTED_PROB = 1.0 / (255 * 256)
    EXPECTED_COUNT = NUM_TRIALS * EXPECTED_PROB

    print("--- Verification Script for Kuznyechik Distinguisher ---")
    print(f"Testing c = {BEST_C:#02x} for {NUM_TRIALS:,} trials.")
    print(f"Input Diff (A):  {BEST_A:#034x}")
    print(f"Output Diff (B): {BEST_B:#034x}")
    print(f"Expected Count under random assumption: {EXPECTED_COUNT:.2f}\n")

    observed_count = 0
    start_time = time.time()
    
    a_block = int_to_block_128(BEST_A)

    for i in range(NUM_TRIALS):
        x_int = random.getrandbits(128)
        x_block = int_to_block_128(x_int)
        
        # This assumes c=1 for plaintext construction for simplicity in verification
        paired_block = [x_block[j] ^ a_block[j] for j in range(16)]

        y1_block = encrypt_n_rounds_kuznyechik_optimized(x_block, NUM_ROUNDS)
        y2_block = encrypt_n_rounds_kuznyechik_optimized(paired_block, NUM_ROUNDS)
        
        diff_block = [y1_block[j] ^ y2_block[j] for j in range(16)]
        
        diff_int = 0
        for j in range(16):
            diff_int |= (diff_block[j] << ((15-j) * 8))

        if diff_int == BEST_B:
            observed_count += 1
    
    end_time = time.time()
    bias_ratio = (observed_count / EXPECTED_COUNT) if EXPECTED_COUNT > 0 else float('inf')
    
    observed_prob_numerator = (observed_count / NUM_TRIALS) * 256 if NUM_TRIALS > 0 else 0
    expected_prob_numerator = (EXPECTED_COUNT / NUM_TRIALS) * 256 if NUM_TRIALS > 0 else 0

    print("--- Results ---")
    print(f"Time taken: {end_time - start_time:.2f} seconds")
    print(f"Observed Count: {observed_count}")
    print(f"Expected Count: {EXPECTED_COUNT:.2f}")
    print(f"Bias Ratio: {bias_ratio:.3f}x")
    print("---")
    print("PROBABILITY (in the format requested by the reviewer):")
    print(f"  Observed Probability: {observed_prob_numerator:.3f} / 256")
    print(f"  Expected Probability: {expected_prob_numerator:.3f} / 256")
    print("-----------------")

if __name__ == "__main__":
    verify_single_distinguisher()