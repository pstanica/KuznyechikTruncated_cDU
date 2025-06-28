## make sure you install statsmodels with `sage -pip install statsmodels'

## ENHANCED VERSION WITH INCREASED SENSITIVITY - Created by Pantelimon Stanica, June 2025
# This version adds multiple sensitivity enhancements while preserving all original functionality
# 
# New Features:
# 1. Multiple testing correction methods (FDR, Holm, Bonferroni, etc.)
# 2. Adaptive significance thresholds based on data characteristics
# 3. Sequential testing with early discovery
# 4. Enhanced bias metrics (KL divergence, entropy measures)
# 5. Combined evidence testing (Fisher's method)
# 6. Clustering analysis for related differentials
# 7. All original tests preserved and enhanced

import sys
import time
import math
import random as py_random
from collections import defaultdict
import multiprocessing as mp
from functools import partial
import os
import secrets
import traceback

# Import all SageMath functions. This is crucial for the ONE-TIME precomputation setup.
# Workers will NOT import this.
from sage.all import *

# Check for NumPy and SciPy availability (optional, for some stats)
NUMPY_AVAILABLE = False
SCIPY_STATS_AVAILABLE = False
STATSMODELS_AVAILABLE = False # Flag for statsmodels

try:
    import numpy as np
    NUMPY_AVAILABLE = True
    try:
        from scipy.stats import skew, kurtosis, shapiro, kstest, chisquare, power_divergence, binom, anderson, combine_pvalues, entropy
        from scipy.spatial.distance import hamming
        from scipy.cluster.hierarchy import fclusterdata
        SCIPY_STATS_AVAILABLE = True
    except ImportError:
        print("Warning: scipy.stats not found. Some statistical tests will be unavailable.")
except ImportError:
    print("Warning: NumPy not found. Some statistical functionalities will be unavailable.")

try:
    from statsmodels.stats.multitest import fdrcorrection, multipletests
    STATSMODELS_AVAILABLE = True
except ImportError:
    print("Warning: statsmodels not found. FDR correction will be unavailable.")


# ==============================================================================
# GLOBAL VARIABLES (MAIN PROCESS - FOR SETUP ONLY)
# ==============================================================================
P = None
x = None
KUZNYECHIK_IRREDUCIBLE_POLY = None
F = None
alpha = None
int_to_gf_SAGE = [] # Maps int to a SAGE GF(2^8) element
gf_to_int_SAGE = {} # Maps SAGE GF(2^8) element to int

# ==============================================================================
# GLOBAL DATA TABLES (MAIN PROCESS - PASSED TO WORKERS)
# ==============================================================================
sbox_int_values = [
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
]

# OPTIMIZED INTEGER-BASED TABLES
SBOX_INT = tuple(sbox_int_values)
INV_SBOX_INT = tuple([SBOX_INT.index(i) for i in range(256)])
GF_MULT_TABLE = [] # 256x256 table for GF(2^8) multiplication
L_TABLE = []       # Precomputed L-transform table: L_TABLE[pos][byte_val] -> 16-byte tuple
L_INV_TABLE = []   # Precomputed L_inv-transform table

EXPANDED_ROUND_KEYS_INT = [] # List of 16-element integer blocks
C_j_values_int = []          # List of 16-element integer blocks for constants

# Global parameters - will be dynamically adjusted based on rounds
MIN_OCCURRENCES_THRESHOLD = 5
STRONG_DIFFERENTIAL_THRESHOLD = 10
MAX_BIAS_THRESHOLD = 2.0
# Significance level for Goodness-of-Fit tests to flag an anomaly
GOF_ANOMALY_THRESHOLD = 0.001

# NEW: Enhanced sensitivity parameters
ENABLE_SEQUENTIAL_TESTING = True
ENABLE_CLUSTERING = True
ENABLE_COMBINED_EVIDENCE = True
ENABLE_ADAPTIVE_ALPHA = True
ENABLE_MULTIPLE_CORRECTIONS = True


# ==============================================================================
# WORKER PROCESS GLOBAL VARIABLES
# ==============================================================================
_SBOX_INT_WORKER = None
_INV_SBOX_INT_WORKER = None
_GF_MULT_TABLE_WORKER = None
_L_TABLE_WORKER = None
_L_INV_TABLE_WORKER = None
_C_j_values_int_WORKER = None
_EXPANDED_ROUND_KEYS_INT_WORKER = None

def _worker_initializer(sbox, inv_sbox, mult_table, l_table, l_inv_table, cj_vals, expanded_keys):
    """Initializes global data tables in each worker process."""
    global _SBOX_INT_WORKER, _INV_SBOX_INT_WORKER, _GF_MULT_TABLE_WORKER
    global _L_TABLE_WORKER, _L_INV_TABLE_WORKER, _C_j_values_int_WORKER, _EXPANDED_ROUND_KEYS_INT_WORKER

    _SBOX_INT_WORKER = sbox
    _INV_SBOX_INT_WORKER = inv_sbox
    _GF_MULT_TABLE_WORKER = mult_table
    _L_TABLE_WORKER = l_table
    _L_INV_TABLE_WORKER = l_inv_table
    _C_j_values_int_WORKER = cj_vals
    _EXPANDED_ROUND_KEYS_INT_WORKER = expanded_keys
    py_random.seed(secrets.randbits(128))


# ==============================================================================
# KUZNYECHIK HELPER FUNCTIONS (OPTIMIZED & PRECOMPUTATION)
# ==============================================================================

def _l_function_slow_for_precomputation(state_bytes_gf: list, coeffs_gf: list) -> object:
    """The original l() function using Sage GF elements. FOR PRECOMPUTATION ONLY."""
    l = state_bytes_gf[15]
    for j in range(14, -1, -1):
        l = l + coeffs_gf[j] * state_bytes_gf[j]
    return l

def _R_transformation_slow_for_precomputation(state_16_bytes_gf: list, coeffs_gf: list) -> list:
    """Original R transform using Sage GF elements. FOR PRECOMPUTATION ONLY."""
    l_val = _l_function_slow_for_precomputation(state_16_bytes_gf, coeffs_gf)
    return [l_val] + state_16_bytes_gf[0:15]

def _L_transformation_slow_for_precomputation(state_16_bytes_gf: list) -> list:
    """Original L transform using Sage GF elements. FOR PRECOMPUTATION ONLY."""
    coeffs = [148, 32, 133, 16, 194, 192, 1, 251, 1, 192, 194, 16, 133, 32, 148, 1]
    coeffs_gf = [int_to_gf_SAGE[c] for c in coeffs]
    state = list(state_16_bytes_gf)
    for _ in range(16):
        state = _R_transformation_slow_for_precomputation(state, coeffs_gf)
    return state

def _R_inverse_transformation_slow_for_precomputation(state_16_bytes_gf: list, coeffs_gf: list) -> list:
    """Original R-inverse using Sage GF elements. FOR PRECOMPUTATION ONLY."""
    c = state_16_bytes_gf[0]
    new_state = state_16_bytes_gf[1:16] + [F(0)]
    sum_val = F(0)
    for j in range(15):
        sum_val = sum_val + coeffs_gf[j] * new_state[j]
    new_state[15] = c + sum_val
    return new_state

def _L_inverse_transformation_slow_for_precomputation(state_16_bytes_gf: list) -> list:
    """Original L-inverse using Sage GF elements. FOR PRECOMPUTATION ONLY."""
    coeffs = [148, 32, 133, 16, 194, 192, 1, 251, 1, 192, 194, 16, 133, 32, 148, 1]
    coeffs_gf = [int_to_gf_SAGE[c] for c in coeffs]
    state = list(state_16_bytes_gf)
    for _ in range(16):
        state = _R_inverse_transformation_slow_for_precomputation(state, coeffs_gf)
    return state

def setup_kuznyechik_precomputation_tables():
    """Initializes all global constants and precomputation tables in the MAIN process."""
    global P, x, KUZNYECHIK_IRREDUCIBLE_POLY, F, alpha, int_to_gf_SAGE, gf_to_int_SAGE
    global GF_MULT_TABLE, L_TABLE, L_INV_TABLE, C_j_values_int

    print("Setting up SageMath environment for one-time precomputation...")
    P = PolynomialRing(GF(2), 'x')
    x = P.gen()
    KUZNYECHIK_IRREDUCIBLE_POLY = x**8 + x**7 + x**6 + x + 1
    F = GF(2**8, name='alpha', modulus=KUZNYECHIK_IRREDUCIBLE_POLY)
    alpha = F.gen()

    for i in range(256):
        poly_coeffs = [(i >> bit) & 1 for bit in range(8)]
        gf_elem_explicit = F(P(poly_coeffs))
        int_to_gf_SAGE.append(gf_elem_explicit)
        gf_to_int_SAGE[gf_elem_explicit] = i

    print("Precomputing GF(2^8) multiplication table...")
    GF_MULT_TABLE = tuple([tuple([gf_to_int_SAGE[int_to_gf_SAGE[i] * int_to_gf_SAGE[j]] for j in range(256)]) for i in range(256)])
    print("✅ Multiplication table created.")

    print("Precomputing L-transformation table...")
    l_table_list = []
    for i in range(16):
        pos_table = tuple([tuple([gf_to_int_SAGE[val] for val in _L_transformation_slow_for_precomputation([F(0)]*i + [int_to_gf_SAGE[b]] + [F(0)]*(15-i))]) for b in range(256)])
        l_table_list.append(pos_table)
    L_TABLE = tuple(l_table_list)
    print("✅ L-transformation table created.")

    print("Precomputing L-inverse-transformation table...")
    l_inv_table_list = []
    for i in range(16):
        pos_table = tuple([tuple([gf_to_int_SAGE[val] for val in _L_inverse_transformation_slow_for_precomputation([F(0)]*i + [int_to_gf_SAGE[b]] + [F(0)]*(15-i))]) for b in range(256)])
        l_inv_table_list.append(pos_table)
    L_INV_TABLE = tuple(l_inv_table_list)
    print("✅ L-inverse-transformation table created.")

    print("Generating Kuznyechik C_j constants...")
    C_j_values_int.append(tuple([0] * 16))
    for j_int in range(1, 33):
        input_vec_gf = [F(0)] * 15 + [int_to_gf_SAGE[j_int]]
        C_j_val_gf = _L_transformation_slow_for_precomputation(input_vec_gf)
        C_j_values_int.append(tuple([gf_to_int_SAGE[val] for val in C_j_val_gf]))
    C_j_values_int = tuple(C_j_values_int)
    print(f"✅ Generated {len(C_j_values_int) - 1} Kuznyechik C_j constants.")

# --- OPTIMIZED INTEGER-BASED FUNCTIONS ---

def L_transformation_optimized(state_int: list) -> list:
    """Optimized L-transformation using precomputed tables and integer XOR."""
    target_L_TABLE = _L_TABLE_WORKER if _L_TABLE_WORKER is not None else L_TABLE
    res = [0] * 16
    for i in range(16):
        row = target_L_TABLE[i][state_int[i]]
        for j in range(16):
            res[j] ^= row[j]
    return res

def L_inverse_transformation_optimized(state_int: list) -> list:
    """Optimized L-inverse-transformation using precomputed tables and integer XOR."""
    target_L_INV_TABLE = _L_INV_TABLE_WORKER if _L_INV_TABLE_WORKER is not None else L_INV_TABLE
    res = [0] * 16
    for i in range(16):
        row = target_L_INV_TABLE[i][state_int[i]]
        for j in range(16):
            res[j] ^= row[j]
    return res

def int_to_block_128(val_int: int) -> list:
    """Converts a 128-bit integer to a list of 16 bytes (integers)."""
    return [(val_int >> ((15-i) * 8)) & 0xFF for i in range(16)]

def block_to_int_128(block_int: list) -> int:
    """Converts a list of 16 bytes (integers) to a 128-bit integer."""
    val = 0
    for i in range(16):
        val |= (block_int[i] << ((15-i) * 8))
    return val

def apply_f_function_optimized(a1_int: list, a0_int: list, Ck_int: list) -> tuple:
    """Applies the F-function using optimized integer operations."""
    sbox = _SBOX_INT_WORKER if _SBOX_INT_WORKER is not None else SBOX_INT
    temp = [a1_int[i] ^ Ck_int[i] for i in range(16)]
    temp = [sbox[byte] for byte in temp]
    lsx_result = L_transformation_optimized(temp)
    new_a1 = [lsx_result[i] ^ a0_int[i] for i in range(16)]
    return new_a1, a1_int

MASTER_KEY_INT_kuznyechik = 0x8899aabbccddeeff0011223344556677fedcba98765432100123456789abcdef

def key_expansion_kuznyechik_optimized(master_key_int: int):
    """Kuznyechik key expansion using optimized integer operations."""
    global EXPANDED_ROUND_KEYS_INT
    EXPANDED_ROUND_KEYS_INT = []

    k2_int = master_key_int & ((1 << 128) - 1)
    k1_int = master_key_int >> 128
    K1 = int_to_block_128(k1_int)
    K2 = int_to_block_128(k2_int)

    EXPANDED_ROUND_KEYS_INT.append(tuple(K1))
    EXPANDED_ROUND_KEYS_INT.append(tuple(K2))

    current_C_j = C_j_values_int
    for i in range(1, 5):
        current_pair = (K1, K2)
        for k in range(8 * (i - 1) + 1, 8 * i + 1):
            Ck = current_C_j[k]
            current_pair = apply_f_function_optimized(current_pair[0], current_pair[1], Ck)
        K1, K2 = current_pair
        EXPANDED_ROUND_KEYS_INT.append(tuple(K1))
        EXPANDED_ROUND_KEYS_INT.append(tuple(K2))
    EXPANDED_ROUND_KEYS_INT = tuple(EXPANDED_ROUND_KEYS_INT)

def encrypt_n_rounds_kuznyechik_optimized(plaintext_int_block: list, num_rounds: int) -> list:
    """Encrypts a single 16-byte integer block for num_rounds."""
    sbox = _SBOX_INT_WORKER if _SBOX_INT_WORKER is not None else SBOX_INT
    keys = _EXPANDED_ROUND_KEYS_INT_WORKER if _EXPANDED_ROUND_KEYS_INT_WORKER is not None else EXPANDED_ROUND_KEYS_INT
    state = [plaintext_int_block[i] ^ keys[0][i] for i in range(16)]
    for r in range(1, num_rounds + 1):
        state = [sbox[byte] for byte in state]
        state = L_transformation_optimized(state)
        state = [state[i] ^ keys[r][i] for i in range(16)]
    return state

def decrypt_n_rounds_kuznyechik_optimized(ciphertext_int_block: list, num_rounds: int) -> list:
    """Decrypts a single 16-byte integer block for num_rounds."""
    inv_sbox = _INV_SBOX_INT_WORKER if _INV_SBOX_INT_WORKER is not None else INV_SBOX_INT
    keys = _EXPANDED_ROUND_KEYS_INT_WORKER if _EXPANDED_ROUND_KEYS_INT_WORKER is not None else EXPANDED_ROUND_KEYS_INT
    state = [ciphertext_int_block[i] ^ keys[num_rounds][i] for i in range(16)]
    for r in range(num_rounds - 1, -1, -1):
        state = L_inverse_transformation_optimized(state)
        state = [inv_sbox[byte] for byte in state]
        state = [state[i] ^ keys[r][i] for i in range(16)]
    return state

def encrypt_n_rounds_batch_optimized(plaintext_blocks_int: list, num_rounds: int) -> list:
    """Encrypts a batch of plaintext blocks using optimized integer operations."""
    sbox = _SBOX_INT_WORKER
    keys = _EXPANDED_ROUND_KEYS_INT_WORKER
    keys_slice = keys[:num_rounds + 1]
    results = []
    for plaintext_block in plaintext_blocks_int:
        state = [plaintext_block[i] ^ keys_slice[0][i] for i in range(16)]
        for r in range(1, num_rounds + 1):
            state = [sbox[byte] for byte in state]
            state = L_transformation_optimized(state)
            state = [state[i] ^ keys_slice[r][i] for i in range(16)]
        results.append(state)
    return results

def truncated_c_differential_uniformity_optimized(c_val_int: int, input_mask: tuple, output_mask: tuple,
                                                 num_rounds: int, trials: int = 10000,
                                                 block_bit_length: int = 128, batch_size: int = 1000) -> tuple:
    """Performs truncated C-differential uniformity analysis using optimized integer operations."""
    mult_table = _GF_MULT_TABLE_WORKER
    counts = defaultdict(int)
    input_nibble_positions = [i for i, active in enumerate(input_mask) if active]
    output_nibble_positions = [i for i, active in enumerate(output_mask) if active]

    def apply_mask_fast(value_int: int, nibble_positions: list) -> int:
        result = 0
        for pos in nibble_positions:
            nibble = (value_int >> (4 * pos)) & 0xF
            result |= (nibble << (4 * pos))
        return result

    non_zero_input_pairs = 0
    for batch_start in range(0, trials, batch_size):
        current_batch_size = min(batch_size, trials - batch_start)
        x_ints = [py_random.getrandbits(block_bit_length) for _ in range(current_batch_size)]
        a_ints = [py_random.getrandbits(block_bit_length) for _ in range(current_batch_size)]
        a_masked_ints = [apply_mask_fast(a, input_nibble_positions) for a in a_ints]

        x_blocks = [int_to_block_128(x) for x in x_ints]
        a_masked_blocks = [int_to_block_128(a) for a in a_masked_ints]

        cx_plus_a_blocks = [[mult_table[c_val_int][x_blocks[i][j]] ^ a_masked_blocks[i][j] for j in range(16)] for i in range(current_batch_size)]

        encrypted_x_blocks = encrypt_n_rounds_batch_optimized(x_blocks, num_rounds)
        encrypted_cx_a_blocks = encrypt_n_rounds_batch_optimized(cx_plus_a_blocks, num_rounds)

        for i in range(current_batch_size):
            diff_block_unmasked = [encrypted_x_blocks[i][j] ^ encrypted_cx_a_blocks[i][j] for j in range(16)]
            diff_int = block_to_int_128(diff_block_unmasked)
            diff_masked = apply_mask_fast(diff_int, output_nibble_positions)
            
            if a_masked_ints[i] != 0:
                non_zero_input_pairs += 1
                counts[(a_masked_ints[i], diff_masked)] += 1
    return counts, non_zero_input_pairs

# ==============================================================================
# NEW ENHANCED SENSITIVITY FUNCTIONS
# ==============================================================================

def calculate_adaptive_alpha(counts: dict, num_rounds: int, base_alpha: float = 0.05) -> float:
    """Calculate data-driven adaptive significance threshold"""
    if not counts or not ENABLE_ADAPTIVE_ALPHA:
        return base_alpha
    
    # Get count values
    count_values = [c for c in counts.values() if c > 0]
    if len(count_values) < 100:
        return base_alpha
    
    if NUMPY_AVAILABLE:
        # Use robust statistics
        q1 = np.percentile(count_values, 25)
        q3 = np.percentile(count_values, 75)
        iqr = q3 - q1
        
        # Adaptive threshold based on data spread
        noise_factor = iqr / np.sqrt(len(count_values))
        adaptive_alpha = base_alpha * (1 + noise_factor * 0.1)
    else:
        # Fallback without numpy
        adaptive_alpha = base_alpha
    
    # More permissive for higher rounds
    round_factor = 1 + max(0, (num_rounds - 5) * 0.1)
    
    return min(adaptive_alpha * round_factor, 0.15)

def calculate_enhanced_bias_metrics(counts: dict, total_trials: int, expected_prob: float) -> dict:
    """Calculate multiple bias detection metrics including KL divergence and entropy"""
    metrics = {}
    
    if not counts or total_trials == 0:
        return metrics
    
    # Kullback-Leibler divergence
    kl_div = 0
    for count in counts.values():
        if count > 0:
            observed_p = count / total_trials
            if expected_prob > 0:
                kl_div += observed_p * np.log(observed_p / expected_prob)
    
    metrics['kl_divergence'] = kl_div
    
    # Chi-square statistics
    chi2_stats = []
    for count in counts.values():
        expected = total_trials * expected_prob
        if expected > 0:
            chi2 = (count - expected)**2 / expected
            chi2_stats.append(chi2)
    
    metrics['max_chi2'] = max(chi2_stats) if chi2_stats else 0
    metrics['sum_chi2'] = sum(chi2_stats)
    
    # Entropy-based measure
    if SCIPY_STATS_AVAILABLE:
        count_probs = [count/total_trials for count in counts.values() if count > 0]
        if count_probs:
            obs_entropy = entropy(count_probs, base=2)
            max_entropy = -np.log2(expected_prob) if expected_prob > 0 else 0
            metrics['relative_entropy'] = obs_entropy / max_entropy if max_entropy > 0 else 0
    
    return metrics

def perform_multiple_testing_corrections(raw_p_values: list, keys_for_p_values: list, 
                                       alpha_level: float = 0.05) -> dict:
    """Apply multiple testing correction methods and return results"""
    results = {}
    
    if not raw_p_values or not ENABLE_MULTIPLE_CORRECTIONS:
        return results
    
    if STATSMODELS_AVAILABLE:
        methods = ['fdr_bh', 'holm', 'bonferroni', 'fdr_by']
        
        for method in methods:
            try:
                rejected, corrected_p = multipletests(raw_p_values, alpha=alpha_level, method=method)[:2]
                results[method] = {
                    'rejected': rejected,
                    'corrected_p_values': corrected_p,
                    'num_significant': sum(rejected)
                }
            except Exception as e:
                print(f"Warning: {method} correction failed: {e}")
    
    return results

def cluster_differential_patterns(statistical_results: list, distance_threshold: float = 0.1) -> dict:
    """Cluster similar differential patterns and perform meta-analysis"""
    if not ENABLE_CLUSTERING or not statistical_results or not SCIPY_STATS_AVAILABLE:
        return {}
    
    # Extract patterns
    patterns = []
    for res in statistical_results:
        # Normalize differentials for clustering
        a_norm = res['a_val'] / (2**128 - 1)
        b_norm = res['b_val'] / (2**128 - 1)
        patterns.append([a_norm, b_norm, res['bias_ratio'], res['p_value']])
    
    if len(patterns) < 2:
        return {}
    
    try:
        # Cluster based on pattern similarity
        patterns_array = np.array(patterns)
        clusters = fclusterdata(patterns_array[:, :2], distance_threshold, 
                              metric='euclidean', criterion='distance')
        
        # Combine p-values within clusters
        cluster_results = {}
        for cluster_id in np.unique(clusters):
            cluster_indices = np.where(clusters == cluster_id)[0]
            cluster_pvals = [patterns[i][3] for i in cluster_indices]
            
            if len(cluster_pvals) > 1:
                # Fisher's method for combining p-values
                combined_stat, combined_p = combine_pvalues(cluster_pvals, method='fisher')
                
                cluster_results[int(cluster_id)] = {
                    'size': len(cluster_indices),
                    'combined_p': combined_p,
                    'member_indices': cluster_indices.tolist(),
                    'avg_bias': np.mean([patterns[i][2] for i in cluster_indices])
                }
        
        return cluster_results
    except Exception as e:
        print(f"Warning: Clustering analysis failed: {e}")
        return {}

def check_combined_evidence_enhanced(statistical_results: list, num_rounds: int, 
                                   config_desc: str, c_val: int) -> dict:
    """Enhanced combined evidence testing using Fisher's method"""
    combined_evidence = {}
    
    if not ENABLE_COMBINED_EVIDENCE or not statistical_results or not SCIPY_STATS_AVAILABLE:
        return combined_evidence
    
    # Multiple evidence thresholds
    evidence_groups = {
        'strong_bias': [r for r in statistical_results if r['bias_ratio'] > 1.4],
        'moderate_bias': [r for r in statistical_results if 1.2 <= r['bias_ratio'] <= 1.4],
        'weak_significant': [r for r in statistical_results if r['p_value'] < 0.2],
        'combined_moderate': [r for r in statistical_results 
                            if r['bias_ratio'] > 1.3 and r['p_value'] < 0.1]
    }
    
    for group_name, group_results in evidence_groups.items():
        if len(group_results) >= 5:  # Require multiple weak signals
            p_values = [r['p_value'] for r in group_results]
            try:
                combined_stat, combined_p = combine_pvalues(p_values, method='fisher')
                
                if combined_p < 0.01:  # Strong combined evidence
                    combined_evidence[group_name] = {
                        'num_signals': len(group_results),
                        'combined_p': combined_p,
                        'avg_bias': np.mean([r['bias_ratio'] for r in group_results])
                    }
                    
                    print(f"\n🔍 COMBINED EVIDENCE ({group_name}): {len(group_results)} signals")
                    print(f"   Config: {config_desc}, c={c_val:#02x}")
                    print(f"   Fisher's combined p-value: {combined_p:.3e}")
                    print(f"   Average bias: {combined_evidence[group_name]['avg_bias']:.2f}x")
            except Exception as e:
                print(f"Warning: Combined evidence test failed for {group_name}: {e}")
    
    return combined_evidence

def sequential_differential_test(c_val_int: int, input_mask: tuple, output_mask: tuple,
                               num_rounds: int, max_trials: int = 10000000,
                               batch_size: int = 500000, alpha: float = 0.05, 
                               beta: float = 0.2) -> tuple:
    """Sequential testing with early stopping for discoveries"""
    if not ENABLE_SEQUENTIAL_TESTING:
        return None, None, []
    
    cumulative_counts = defaultdict(int)
    total_trials = 0
    
    # Sequential probability ratio test parameters
    log_lr_threshold_accept = np.log((1-beta)/alpha) if alpha > 0 and beta < 1 else 5
    log_lr_threshold_reject = np.log(beta/(1-alpha)) if alpha < 1 and beta > 0 else -5
    
    num_input_active = sum(input_mask)
    num_output_active = sum(output_mask)
    expected_prob = 1.0 / ((2**(4*num_input_active) - 1) * 2**(4*num_output_active))
    
    print(f"Starting sequential testing (max {max_trials:,} trials, batch {batch_size:,})...")
    
    for batch_num in range(max_trials // batch_size):
        # Run batch
        batch_counts, non_zero = truncated_c_differential_parallel(
            c_val_int, input_mask, output_mask, num_rounds, 
            trials=batch_size, block_bit_length=128)
        
        # Update cumulative counts
        for key, count in batch_counts.items():
            cumulative_counts[key] += count
        total_trials += batch_size
        
        # Check for early discoveries
        significant_found = []
        for (a_val, b_val), obs_count in cumulative_counts.items():
            if a_val == 0 or obs_count < 3:
                continue
            
            # Calculate log likelihood ratio
            observed_prob = obs_count / total_trials
            if observed_prob > expected_prob * 1.5:  # Only test if bias > 1.5
                llr = obs_count * np.log(observed_prob / expected_prob)
                
                if llr > log_lr_threshold_accept:
                    p_value = binomial_test_p_value(obs_count, total_trials, expected_prob)
                    significant_found.append({
                        'a_val': a_val, 
                        'b_val': b_val, 
                        'count': obs_count,
                        'llr': llr,
                        'p_value': p_value,
                        'bias': observed_prob / expected_prob
                    })
        
        if significant_found:
            print(f"✨ Sequential early discovery at {total_trials:,} trials!")
            for sig in significant_found[:3]:
                print(f"   {sig['a_val']:#034x} → {sig['b_val']:#034x}")
                print(f"   Bias: {sig['bias']:.2f}x, LLR: {sig['llr']:.1f}, p: {sig['p_value']:.3e}")
            return cumulative_counts, total_trials, significant_found
        
        # Progress update
        if (batch_num + 1) % 5 == 0:
            print(f"   Sequential progress: {total_trials:,} trials, "
                  f"tracking {len(cumulative_counts)} pairs")
    
    return cumulative_counts, total_trials, []

# ==============================================================================
# ANALYSIS, VALIDATION, AND EXECUTION (Original + Enhanced)
# ==============================================================================

def process_chunk(args):
    """Wrapper function for multiprocessing.Pool."""
    c_val_int, input_mask, output_mask, num_rounds, chunk_size, block_bit_length = args
    return truncated_c_differential_uniformity_optimized(
        c_val_int, input_mask, output_mask, num_rounds,
        trials=chunk_size, block_bit_length=block_bit_length,
        batch_size=min(chunk_size, 2000))

def truncated_c_differential_parallel(c_val_int: int, input_mask: tuple, output_mask: tuple,
                                     num_rounds: int, trials: int = 10000,
                                     block_bit_length: int = 128, num_processes: int = None) -> tuple:
    """Runs truncated C-differential uniformity analysis in parallel."""
    if num_processes is None:
        num_processes = mp.cpu_count()
    use_parallel = num_processes > 1 and trials >= num_processes * 1000

    if not use_parallel:
        print(f"Detected {num_processes} CPU cores. Running in single process mode.")
        _worker_initializer(SBOX_INT, INV_SBOX_INT, GF_MULT_TABLE, L_TABLE, L_INV_TABLE, C_j_values_int, EXPANDED_ROUND_KEYS_INT)
        return truncated_c_differential_uniformity_optimized(
            c_val_int, input_mask, output_mask, num_rounds=num_rounds,
            trials=trials, block_bit_length=block_bit_length)

    print(f"Detected {num_processes} CPU cores. Using {num_processes} processes for this run.")
    initializer_args = (SBOX_INT, INV_SBOX_INT, GF_MULT_TABLE, L_TABLE, L_INV_TABLE, C_j_values_int, EXPANDED_ROUND_KEYS_INT)
    chunk_size = trials // num_processes
    tasks = [(c_val_int, input_mask, output_mask, num_rounds, (chunk_size if i < num_processes - 1 else trials - chunk_size * (num_processes - 1)), block_bit_length)
             for i in range(num_processes) if (chunk_size if i < num_processes - 1 else trials - chunk_size * (num_processes - 1)) > 0]

    combined_counts = defaultdict(int)
    total_non_zero_trials = 0
    with mp.Pool(num_processes, initializer=_worker_initializer, initargs=initializer_args) as pool:
        chunk_results = pool.map(process_chunk, tasks)

    for chunk_counts, non_zero_count in chunk_results:
        total_non_zero_trials += non_zero_count
        for key, count in chunk_counts.items():
            combined_counts[key] += count
    return combined_counts, total_non_zero_trials

def binomial_test_p_value(observed_count: int, total_trials: int, expected_prob: float) -> float:
    """Calculates the two-tailed p-value for a binomial test."""
    if not (0.0 <= expected_prob <= 1.0) or total_trials <= 0: return 1.0
    if expected_prob == 0: return 0.0 if observed_count > 0 else 1.0
    if SCIPY_STATS_AVAILABLE:
        p_lower = binom.cdf(observed_count, total_trials, expected_prob)
        p_upper = 1 - binom.cdf(observed_count - 1, total_trials, expected_prob)
        return min(1.0, 2 * min(p_lower, p_upper))
    else:
        return 1.0

def calculate_bias_statistics(observed_count: int, total_trials: int, expected_prob: float) -> dict:
    """Calculates bias ratio and p-value for an observed count."""
    if total_trials <= 0:
        return {'observed_count': 0, 'expected_count': 0, 'bias_ratio': 0.0, 'p_value': 1.0}
    expected_count = total_trials * expected_prob
    bias_ratio = (observed_count / expected_count) if expected_count > 1e-10 else (float('inf') if observed_count > 0 else 0.0)
    if bias_ratio > 1e6: bias_ratio = float('inf')
    p_value = binomial_test_p_value(observed_count, total_trials, expected_prob)
    return {'observed_count': observed_count, 'expected_count': expected_count, 'bias_ratio': bias_ratio, 'p_value': p_value}

def comprehensive_statistical_analysis(counts: defaultdict, input_mask: tuple, output_mask: tuple,
                                        actual_trials: int, alpha_level: float = 0.001,
                                        num_rounds: int = None) -> tuple:
    """Enhanced comprehensive statistical analysis with multiple testing corrections"""
    statistical_results = []
    num_input_active_nibbles = sum(input_mask)
    num_output_active_nibbles = sum(output_mask)
    input_diff_space_size = 2**(4 * num_input_active_nibbles)
    output_diff_space_size = 2**(4 * num_output_active_nibbles)
    total_possible_non_zero_masked_pairs = (input_diff_space_size - 1) * output_diff_space_size
    expected_prob = 1.0 / total_possible_non_zero_masked_pairs if total_possible_non_zero_masked_pairs > 0 else 0.0

    # Calculate adaptive alpha if enabled
    adaptive_alpha = calculate_adaptive_alpha(counts, num_rounds, alpha_level)
    
    raw_p_values = []
    keys_for_p_values = []
    
    # Track uncorrected significant results
    uncorrected_significant_results = []

    for (a_val, b_val), observed_count in counts.items():
        if a_val == 0: continue
        if observed_count >= MIN_OCCURRENCES_THRESHOLD and expected_prob > 0:
            p_value = binomial_test_p_value(observed_count, actual_trials, expected_prob)
            raw_p_values.append(p_value)
            keys_for_p_values.append((a_val, b_val, observed_count))
            
            # Track uncorrected significant results
            if p_value < 0.05:
                stats = calculate_bias_statistics(observed_count, actual_trials, expected_prob)
                stats['a_val'] = a_val
                stats['b_val'] = b_val
                stats['p_value'] = p_value
                uncorrected_significant_results.append(stats)

    if not raw_p_values:
        return [], expected_prob, alpha_level, uncorrected_significant_results, {}

    # Apply multiple testing corrections
    multiple_corrections = perform_multiple_testing_corrections(
        raw_p_values, keys_for_p_values, adaptive_alpha)
    
    # Use FDR as primary method
    if STATSMODELS_AVAILABLE:
        rejected, corrected_p_values = fdrcorrection(raw_p_values, alpha=adaptive_alpha)
    else:
        print("Warning: statsmodels not available. Skipping FDR correction.")
        rejected = [p < adaptive_alpha for p in raw_p_values]
        corrected_p_values = raw_p_values

    for i, (a_val, b_val, observed_count) in enumerate(keys_for_p_values):
        stats = calculate_bias_statistics(observed_count, actual_trials, expected_prob)
        stats['a_val'] = a_val
        stats['b_val'] = b_val
        stats['p_value'] = raw_p_values[i]
        stats['corrected_p_value'] = corrected_p_values[i]
        stats['is_significant_corrected'] = rejected[i]
        
        # Add results from other correction methods
        stats['correction_results'] = {}
        for method, results in multiple_corrections.items():
            stats['correction_results'][method] = {
                'corrected_p': results['corrected_p_values'][i],
                'is_significant': results['rejected'][i]
            }
        
        statistical_results.append(stats)

    statistical_results.sort(key=lambda x: x['corrected_p_value'])
    
    # Add enhanced metrics
    enhanced_metrics = calculate_enhanced_bias_metrics(counts, actual_trials, expected_prob)
    
    return statistical_results, expected_prob, adaptive_alpha, uncorrected_significant_results, enhanced_metrics

def analyze_distribution_properties(counts: defaultdict) -> dict:
    """Analyzes statistical properties of the observed counts distribution,
    including normality tests for the distribution of observed counts."""
    observed_counts_values = [count for (a_val, b_val), count in counts.items() if a_val != 0]
    props = {'total_pairs': len(observed_counts_values), 'non_zero_pairs': sum(1 for c in observed_counts_values if c > 0)}
    if not observed_counts_values or not NUMPY_AVAILABLE:
        props['shapiro_skipped'] = True
        props['anderson_skipped'] = True
        return props

    np_counts = np.array(observed_counts_values)
    props.update({'mean_count': np.mean(np_counts), 'median_count': np.median(np_counts),
                  'std_count': np.std(np_counts), 'max_count': np.max(np_counts), 'min_count': np.min(np_counts)})
    
    if not SCIPY_STATS_AVAILABLE:
        props['shapiro_skipped'] = True
        props['anderson_skipped'] = True
        return props

    props.update({'skewness': skew(np_counts), 'kurtosis': kurtosis(np_counts)})
    
    if len(np_counts) > 1:
        # Shapiro-Wilk Test
        if len(np_counts) < 5000:
            try:
                props['normality_stat_shapiro'], props['normality_p_shapiro'] = shapiro(np_counts)
                props['shapiro_skipped'] = False
            except ValueError:
                props['normality_stat_shapiro'], props['normality_p_shapiro'] = float('nan'), 1.0
                props['shapiro_skipped'] = False
            except Exception as e:
                print(f"Warning: Shapiro-Wilk test failed unexpectedly: {e}")
                props['shapiro_skipped'] = True
        else:
            props['shapiro_skipped'] = True
            props['shapiro_skip_reason'] = "Dataset too large for Shapiro-Wilk (N >= 5000)"

        # Anderson-Darling Test
        try:
            ad_stat, ad_crit, ad_sig = anderson(np_counts, dist='norm')
            props.update({
                'normality_stat_AD': ad_stat,
                'normality_crit_AD': ad_crit.tolist(),
                'normality_sig_levels_AD': ad_sig.tolist(),
                'is_normal_AD_alpha_15': ad_stat < ad_crit[2],
                'anderson_skipped': False
            })
        except Exception as e:
            print(f"Warning: Anderson-Darling test failed unexpectedly: {e}")
            props['anderson_skipped'] = True
    else:
        props['shapiro_skipped'] = True
        props['anderson_skipped'] = True
        props['normality_skip_reason'] = "Not enough unique pairs for normality tests"
        
    return props

def perform_goodness_of_fit_tests(counts: defaultdict, total_possible_pairs: int, actual_trials: int):
    """
    Performs Chi-square and G-test for goodness of fit against a uniform distribution.
    """
    if not SCIPY_STATS_AVAILABLE or actual_trials == 0:
        return {'gof_skipped': True, 'gof_skip_reason': 'SciPy not available or no trials run'}

    observed_frequencies = [count for (a_val, b_val), count in counts.items() if a_val != 0]
    num_observed_pairs = len(observed_frequencies)

    num_zero_counts = total_possible_pairs - num_observed_pairs
    full_observed = observed_frequencies + ([0] * num_zero_counts)

    expected_count = actual_trials / total_possible_pairs
    
    if expected_count < 5:
        return {'gof_skipped': True, 'gof_skip_reason': f'Expected count per cell ({expected_count:.2f}) is too low for a reliable test.'}

    results = {'gof_skipped': False}
    try:
        chi2_stat, chi2_p = chisquare(f_obs=full_observed)
        results['chi2_stat'] = chi2_stat
        results['chi2_p'] = chi2_p

        g_stat, g_p = power_divergence(f_obs=full_observed, lambda_=0)
        results['g_stat'] = g_stat
        results['g_p'] = g_p

        results['dof'] = total_possible_pairs - 1
    except Exception as e:
        results = {'gof_skipped': True, 'gof_skip_reason': f'SciPy error during test: {e}'}
            
    return results

def calculate_expected_bias_decay(num_rounds: int) -> float:
    """Estimate expected bias after num_rounds assuming exponential decay"""
    # Model: bias should decay exponentially with rounds
    # Adjust based on cipher properties - this is a rough approximation
    return 2.0 ** (-num_rounds / 3.0)

def check_bias_persistence_anomaly(max_bias: float, num_rounds: int, config_desc: str, c_val: int):
    """Check if the observed bias is anomalously high compared to expected decay"""
    expected_bias = calculate_expected_bias_decay(num_rounds)
    ratio = max_bias / expected_bias if expected_bias > 0 else float('inf')
    
    if ratio > 5.0:  # Bias is 5x higher than expected
        print(f"\n⚠️  BIAS PERSISTENCE ANOMALY for {num_rounds} rounds")
        print(f"    Config: {config_desc}, c={c_val:#02x}")
        print(f"    Observed bias: {max_bias:.2f}x vs Expected: {expected_bias:.3f}x")
        print(f"    Ratio: {ratio:.1f}x higher than expected decay")
        return True
    return False

def check_combined_significance(statistical_results: list, num_rounds: int, config_desc: str, c_val: int) -> bool:
    """Check for results that are moderately significant in multiple ways"""
    if num_rounds >= 9:
        # For 9+ rounds, flag results with moderate bias AND moderate p-value
        combined_significant = [
            r for r in statistical_results 
            if r['bias_ratio'] > 1.3 and r['p_value'] < 0.1
        ]
        
        if combined_significant:
            print(f"\n📊 COMBINED SIGNIFICANCE DETECTED for {num_rounds} rounds")
            print(f"   Config: {config_desc}, c={c_val:#02x}")
            print(f"   Found {len(combined_significant)} pairs with bias > 1.3 AND p < 0.1")
            
            # Show top 3
            for res in combined_significant[:3]:
                a_hex, b_hex = f"{res['a_val']:#034x}", f"{res['b_val']:#034x}"
                bias_str = "inf" if res['bias_ratio'] == float('inf') else f"{res['bias_ratio']:.2f}"
                print(f"     - {a_hex} → {b_hex} (Bias: {bias_str}x, p: {res['p_value']:.3f})")
            return True
    return False

def print_detailed_statistical_report(statistical_results: list, dist_props: dict, gof_results: dict,
                                      config_desc: str, c_val: int, alpha: float, 
                                      uncorrected_significant: list = None, num_rounds: int = None,
                                      enhanced_metrics: dict = None, cluster_results: dict = None,
                                      combined_evidence: dict = None):
    """Enhanced statistical report with new sensitivity measures"""
    print(f"\n" + "="*80 + f"\nDETAILED STATISTICAL ANALYSIS for c={c_val:#02x}, {config_desc}\n" + "="*80)
    print(f"DISTRIBUTION PROPERTIES:\n"
          f"  Total unique pairs observed: {dist_props.get('total_pairs', 'N/A'):,}\n"
          f"  Mean/Median/Std Dev count: {dist_props.get('mean_count', 0.0):.2f} / {dist_props.get('median_count', 0.0):.2f} / {dist_props.get('std_count', 0.0):.2f}\n"
          f"  Max/Min count: {dist_props.get('max_count', 0):,} / {dist_props.get('min_count', 0):,}\n"
          f"  Skewness/Kurtosis: {dist_props.get('skewness', 0.0):.3f} / {dist_props.get('kurtosis', 0.0):.3f}")

    # Enhanced metrics
    if enhanced_metrics:
        print("\nENHANCED BIAS METRICS:")
        print(f"  KL Divergence: {enhanced_metrics.get('kl_divergence', 0):.6f}")
        print(f"  Max Chi-square: {enhanced_metrics.get('max_chi2', 0):.2f}")
        print(f"  Relative Entropy: {enhanced_metrics.get('relative_entropy', 0):.3f}")

    # Normality Tests
    print("\nNORMALITY TESTS (on the distribution of observed counts):")
    if dist_props.get('shapiro_skipped'):
        print(f"  Shapiro-Wilk Test: Skipped. Reason: {dist_props.get('shapiro_skip_reason', 'Not applicable or N/A')}")
    else:
        print(f"  Shapiro-Wilk Test: Statistic={dist_props.get('normality_stat_shapiro', float('nan')):.3f}, P-value={dist_props.get('normality_p_shapiro', float('nan')):.3e}")
        print(f"    (Interpretation: P < 0.05 suggests non-normal distribution)")

    if dist_props.get('anderson_skipped'):
        print(f"  Anderson-Darling Test: Skipped. Reason: {dist_props.get('normality_skip_reason', 'Not applicable or N/A')}")
    else:
        print(f"  Anderson-Darling Test: Statistic={dist_props.get('normality_stat_AD', float('nan')):.3f}")
        print(f"    Critical Values (Sig Levels): {dist_props.get('normality_crit_AD', 'N/A')} ({dist_props.get('normality_sig_levels_AD', 'N/A')})")
        print(f"    (Interpretation: Statistic > Critical Value at a given significance level suggests non-normal distribution)")

    print("\nGOODNESS-OF-FIT TESTS (vs. Uniform Distribution):")
    if gof_results.get('gof_skipped'):
        print(f"  Skipped. Reason: {gof_results.get('gof_skip_reason', 'N/A')}")
    else:
        dof = gof_results.get('dof', 'N/A')
        print(f"  (Evaluates if the overall distribution of {dof+1:,} pairs is uniform. Degrees of freedom: {dof:,})")
        print(f"  Chi-square Test: Statistic={gof_results.get('chi2_stat', 0.0):,.2f}, P-value={gof_results.get('chi2_p', 1.0):.3e}")
        print(f"  G-test (Log-likelihood): Statistic={gof_results.get('g_stat', 0.0):,.2f}, P-value={gof_results.get('g_p', 1.0):.3e}")
        print(f"    (Interpretation: A very small P-value, e.g., < {GOF_ANOMALY_THRESHOLD:.3f}, provides strong evidence that the cipher's")
        print(f"     output for this configuration is not uniformly distributed as a whole.)")
    
    # Clustering results
    if cluster_results:
        print("\nCLUSTER ANALYSIS:")
        significant_clusters = [c for c in cluster_results.values() if c['combined_p'] < 0.05]
        print(f"  Found {len(cluster_results)} clusters, {len(significant_clusters)} significant")
        for cid, cdata in sorted(cluster_results.items(), key=lambda x: x[1]['combined_p'])[:3]:
            print(f"  Cluster {cid}: {cdata['size']} members, combined p={cdata['combined_p']:.3e}, avg bias={cdata['avg_bias']:.2f}x")
    
    # Report uncorrected significant results for high rounds
    if uncorrected_significant and num_rounds and num_rounds >= 9:
        print(f"\nUNCORRECTED SIGNIFICANT PAIRS (raw p < 0.05, before FDR):")
        print(f"  Found {len(uncorrected_significant)} pairs significant before correction")
        if len(uncorrected_significant) > 0:
            print(f"  Top 5 by raw p-value:")
            for res in uncorrected_significant[:5]:
                bias_str = "inf" if res['bias_ratio'] == float('inf') else f"{res['bias_ratio']:.2f}"
                print(f"    {res['a_val']:#034x} → {res['b_val']:#034x} (Bias: {bias_str}x, p: {res['p_value']:.3f})")
    
    print(f"\nSIGNIFICANT DIFFERENTIAL PAIRS (FDR-corrected p < {alpha:.3e}):")
    print("  (These are specific (Input Diff, Output Diff) pairs whose observed frequencies")
    print("   are statistically different from expected, after multiple-test correction.)")
    
    significant_pairs = [r for r in statistical_results if r['is_significant_corrected']]
    if not significant_pairs:
        print("  No pairs met the corrected significance threshold.")
        
        # Check if other correction methods found significance
        if statistical_results and 'correction_results' in statistical_results[0]:
            for method in ['holm', 'bonferroni']:
                method_sig = [r for r in statistical_results 
                            if r.get('correction_results', {}).get(method, {}).get('is_significant', False)]
                if method_sig:
                    print(f"\n  Note: {len(method_sig)} pairs significant under {method} correction")
    else:
        print(f"  Found {len(significant_pairs)} significant pairs. Top 10 by corrected p-value:")
        print(f"  {'Input Diff (A)':<33} {'Output Diff (B)':<33} {'Obs Count':<10} {'Bias':<8} {'Corr P-val':<12}")
        print(f"  {'-'*33} {'-'*33} {'-'*10} {'-'*8} {'-'*12}")
        for res in significant_pairs[:10]:
            bias_str = "inf" if res['bias_ratio'] == float('inf') else f"{res['bias_ratio']:.1f}"
            print(f"  {res['a_val']:#034x} {res['b_val']:#034x} {res['observed_count']:<10} {bias_str:<8}x {res['corrected_p_value']:.2e}")
    print("="*80)

def enhanced_truncated_c_differential_analysis(c_val_int: int, input_mask: tuple, output_mask: tuple, config_desc: str,
                                              num_rounds: int, trials: int, block_bit_length: int,
                                              enable_sequential: bool = False) -> dict:
    """Enhanced C-differential analysis with new sensitivity features"""
    
    # Try sequential testing first if enabled
    sequential_results = None
    if enable_sequential and ENABLE_SEQUENTIAL_TESTING:
        seq_counts, seq_trials, seq_discoveries = sequential_differential_test(
            c_val_int, input_mask, output_mask, num_rounds, 
            max_trials=trials * 2, batch_size=min(trials // 10, 1000000))
        
        if seq_discoveries:
            sequential_results = {
                'discoveries': seq_discoveries,
                'trials_used': seq_trials
            }
            # Use sequential counts for further analysis
            counts, actual_trials = seq_counts, seq_trials
        else:
            # Fall back to regular testing
            counts, actual_trials = truncated_c_differential_parallel(
                c_val_int, input_mask, output_mask, num_rounds, trials, block_bit_length)
    else:
        counts, actual_trials = truncated_c_differential_parallel(
            c_val_int, input_mask, output_mask, num_rounds, trials, block_bit_length)

    if actual_trials == 0:
        print("Warning: No non-zero input differentials tested. Skipping stats.")
        return {'statistical_results': [], 'distribution_properties': {}, 'gof_results': {}, 
                'expected_prob': 0.0, 'alpha_level_used': 1.0, 'config_desc': config_desc, 
                'c_val': c_val_int, 'uncorrected_significant': [], 'enhanced_metrics': {}}

    # Dynamic alpha level based on rounds
    if num_rounds >= 9:
        alpha_level = 0.05  # More permissive for high rounds
    elif num_rounds >= 7:
        alpha_level = 0.01
    else:
        alpha_level = 0.005
        
    statistical_results, expected_prob, alpha_level_used, uncorrected_significant, enhanced_metrics = comprehensive_statistical_analysis(
        counts, input_mask, output_mask, actual_trials, alpha_level=alpha_level, num_rounds=num_rounds)
    
    distribution_properties = analyze_distribution_properties(counts)

    # Calculate the total number of possible non-zero pairs for the GoF tests
    num_input_active_nibbles = sum(input_mask)
    num_output_active_nibbles = sum(output_mask)
    input_diff_space_size = 2**(4 * num_input_active_nibbles)
    output_diff_space_size = 2**(4 * num_output_active_nibbles)
    total_possible_non_zero_masked_pairs = (input_diff_space_size - 1) * output_diff_space_size
    
    gof_results = perform_goodness_of_fit_tests(counts, total_possible_non_zero_masked_pairs, actual_trials)
    
    # Perform clustering analysis
    cluster_results = cluster_differential_patterns(statistical_results)
    
    # Check combined evidence
    combined_evidence = check_combined_evidence_enhanced(
        statistical_results, num_rounds, config_desc, c_val_int)

    return {
        'statistical_results': statistical_results, 
        'distribution_properties': distribution_properties,
        'gof_results': gof_results,
        'expected_prob': expected_prob, 
        'alpha_level_used': alpha_level_used,
        'config_desc': config_desc, 
        'c_val': c_val_int,
        'uncorrected_significant': uncorrected_significant,
        'enhanced_metrics': enhanced_metrics,
        'cluster_results': cluster_results,
        'combined_evidence': combined_evidence,
        'sequential_results': sequential_results
    }

def validate_implementation():
    """Validates Kuznyechik implementation against RFC 7801 test vectors using optimized functions."""
    global EXPANDED_ROUND_KEYS_INT
    print("\n--- Validating against RFC 7801 Test Vector ---")
    test_key_int = 0x8899aabbccddeeff0011223344556677fedcba98765432100123456789abcdef
    test_plaintext_int = 0x1122334455667700ffeeddccbbaa9988
    expected_ciphertext_int = 0x7f679d90bebc24305a468d42b9d4edcd

    original_keys = EXPANDED_ROUND_KEYS_INT
    key_expansion_kuznyechik_optimized(test_key_int)

    rfc_expected_keys = [0x8899aabbccddeeff0011223344556677, 0xfedcba98765432100123456789abcdef,
                         0xdb31485315694343228d6aef8cc78c44, 0x3d4553d8e9cfec6815ebadc40a9ffd04,
                         0x57646468c44a5e28d3e59246f429f1ac, 0xbd079435165c6432b532e82834da581b,
                         0x51e640757e8745de705727265a0098b1, 0x5a7925017b9fdd3ed72a91a22286f984,
                         0xbb44e25378c73123a5f32f73cdb6e517, 0x72e9dd7416bcf45b755dbaa88e4a4043]

    print("Comparing generated keys with RFC 7801 expected values:")
    keys_match = all(block_to_int_128(list(actual)) == expected for actual, expected in zip(EXPANDED_ROUND_KEYS_INT, rfc_expected_keys))

    plaintext_block = int_to_block_128(test_plaintext_int)
    encrypted_block = encrypt_n_rounds_kuznyechik_optimized(plaintext_block, 9)
    actual_ciphertext_int = block_to_int_128(encrypted_block)
    encryption_match = actual_ciphertext_int == expected_ciphertext_int
    
    EXPANDED_ROUND_KEYS_INT = original_keys
    if keys_match and encryption_match:
        print("✅ COMPLETE SUCCESS: All keys and encryption match RFC 7801!")
        return True
    else:
        print("❌ VALIDATION FAILED!")
        return False

def get_focused_c_values_noteworthy() -> list:
    """Returns a focused list of c-values for analysis."""
    return [0x01, 0x02, 0x03, 0x04, 0x91, 0xbe, 0xe1]

def generate_mask_configs_noteworthy(num_nibbles=32):
    """
    Generates mask configurations based on the 'noteworthy' findings provided by the user.
    """
    configs = []
    
    def create_byte_mask(byte_index, num_nibbles):
        mask = [False] * num_nibbles
        mask[byte_index * 2] = True
        mask[byte_index * 2 + 1] = True
        return tuple(mask)

    noteworthy_patterns_curated = [
        # Top patterns from 9-round summary
        (0xe1, "byte_4_in->byte_4_out"),
        (0x01, "byte_2_in->byte_2_out"),
        (0xbe, "byte_2_in->byte_2_out"),
        (0xe1, "byte_6_in->byte_6_out"),
        (0x91, "byte_12_in->byte_12_out"),
        (0x91, "byte_0_in->byte_0_out"),
        (0xbe, "byte_14_in->byte_14_out"),
        (0x03, "byte_6_in->byte_6_out"),
        (0x91, "byte_2_in->byte_2_out"),
        (0x03, "byte_10_in->byte_10_out"),
        (0x01, "byte_8_in->byte_8_out"),
        (0xe1, "byte_12_in->byte_12_out"),
        (0x04, "byte_2_in->byte_2_out"),
        (0x04, "byte_8_in->byte_8_out"),
        (0x01, "byte_12_in->byte_12_out"),
        (0xe1, "byte_2_in->byte_2_out"),
        (0x03, "byte_12_in->byte_12_out"),
        (0x02, "byte_12_in->byte_12_out"),
        (0xe1, "byte_8_in->byte_8_out"),
        (0x03, "byte_4_in->byte_4_out"),
        (0x02, "byte_14_in->byte_15_out"),
        (0x02, "byte_0_in->byte_1_out"),
        # --- Hypothesized diffusion patterns based on high-bias (i->i) entries
        (0xe1, "byte_4_in->byte_5_out"),
        (0x01, "byte_2_in->byte_3_out"),
        (0x91, "byte_0_in->byte_1_out"),
        (0xbe, "byte_14_in->byte_15_out"),
        # --- Additional high-bias (but high p-value) patterns from Data_R9.txt
        (0x01, "byte_0_in->byte_0_out"),
        (0xbe, "byte_0_in->byte_0_out"),
        (0x03, "byte_0_in->byte_0_out"),
        (0x04, "byte_4_in->byte_4_out"),
        (0x02, "byte_2_in->byte_2_out"),
        (0x01, "byte_6_in->byte_6_out"),
        (0x91, "byte_8_in->byte_8_out"),
        (0x02, "byte_8_in->byte_8_out"),
        (0x91, "byte_4_in->byte_4_out"),
        (0xbe, "byte_6_in->byte_6_out"),
    ]

    unique_configs = set()

    for c_val, desc_template in noteworthy_patterns_curated:
        try:
            parts_in = desc_template.split('_in->')[0].split('_')
            input_byte_index = int(parts_in[1]) if len(parts_in) > 1 else None

            parts_out = desc_template.split('->')[1].split('_out')[0].split('_')
            output_byte_index = int(parts_out[1]) if len(parts_out) > 1 else None

            if input_byte_index is not None and output_byte_index is not None:
                input_mask = create_byte_mask(input_byte_index, num_nibbles)
                output_mask = create_byte_mask(output_byte_index, num_nibbles)
                unique_configs.add((c_val, input_mask, output_mask, desc_template))
            else:
                print(f"Warning: Could not fully parse byte indices from description: {desc_template}. Skipping.")

        except (IndexError, ValueError) as e:
            print(f"Warning: Error parsing description '{desc_template}': {e}. Skipping configuration.")
            continue

    configs = sorted(list(unique_configs), key=lambda x: (x[0], x[3])) 

    print(f"Generated {len(configs)} mask configurations based on curated noteworthy findings.")
    return configs

def check_early_termination(statistical_results: list, config_desc: str, c_val: int, num_rounds: int,
                           combined_evidence: dict = None) -> bool:
    """Enhanced early termination with combined evidence"""
    significant_pairs = [r for r in statistical_results if r['is_significant_corrected']]
    max_bias = max([r['bias_ratio'] for r in statistical_results] or [0.0])
    
    strong_differential_found = False
    
    if len(significant_pairs) >= STRONG_DIFFERENTIAL_THRESHOLD:
        strong_differential_found = True
        print(f"\n🚨 CRITICAL ALERT: Statistically significant characteristic found for {num_rounds} rounds!")
        print(f"   Config: {config_desc}, c={c_val:#02x}")
        print(f"   Found {len(significant_pairs)} significant pairs (threshold: {STRONG_DIFFERENTIAL_THRESHOLD}).")
    elif combined_evidence and any(ev['combined_p'] < 0.001 for ev in combined_evidence.values()):
        strong_differential_found = True
        print(f"\n🔬 COMBINED EVIDENCE ALERT: Strong combined signal detected!")
        for ev_type, ev_data in combined_evidence.items():
            if ev_data['combined_p'] < 0.001:
                print(f"   {ev_type}: {ev_data['num_signals']} signals, combined p={ev_data['combined_p']:.3e}")
    elif max_bias >= MAX_BIAS_THRESHOLD:
        print(f"\n- NOTICE: High bias detected for {num_rounds} rounds (but not FDR-significant).")
        print(f"   Config: {config_desc}, c={c_val:#02x}")
        print(f"   Max bias ratio: {max_bias:.1f}x (threshold: {MAX_BIAS_THRESHOLD:.1f}x).")
        print("   NOTE: This bias did not meet the False Discovery Rate significance threshold and may be statistical noise.")

    if strong_differential_found:
        sorted_by_p_val = sorted(significant_pairs, key=lambda x: x['corrected_p_value'])
        for result in sorted_by_p_val[:5]:
            a_hex, b_hex = f"{result['a_val']:#034x}", f"{result['b_val']:#034x}"
            bias_str = "inf" if result['bias_ratio'] == float('inf') else f"{result['bias_ratio']:.1f}"
            print(f"     - Input {a_hex} -> Output {b_hex} (Bias: {bias_str}, p-val: {result['corrected_p_value']:.2e})")
    
    return strong_differential_found

def check_gof_anomaly(gof_results: dict, config_desc: str, c_val: int, num_rounds: int):
    """Checks the Goodness-of-Fit p-value and prints an anomaly message if it's below a threshold."""
    if not gof_results or gof_results.get('gof_skipped'):
        return

    p_value = gof_results.get('g_p', 1.0)
    
    if p_value < GOF_ANOMALY_THRESHOLD:
        print(f"\n*** NON-RANDOMNESS ANOMALY DETECTED (Global Distribution) ***")
        print(f"    Config: {config_desc}, c={c_val:#02x}, Rounds: {num_rounds}")
        print(f"    The overall distribution of output differentials is NOT UNIFORM.")
        print(f"    G-test p-value: {p_value:.3e} is less than the threshold of {GOF_ANOMALY_THRESHOLD:.3e}.")
        print(f"    This provides strong statistical evidence of a non-random property for this configuration.")

def run_kuznyechik_analysis():
    """Main function to run the complete enhanced analysis."""
    output_filename = "Multiproc_cDU_Enhanced_Kuznyechik_R8.txt"
    original_stdout = sys.stdout
    try:
        with open(output_filename, 'w') as f:
            sys.stdout = f
            print("Starting Enhanced Kuznyechik C-Differential Cryptanalysis with Increased Sensitivity...")
            print("\nNew features enabled:")
            print(f"  - Sequential testing: {ENABLE_SEQUENTIAL_TESTING}")
            print(f"  - Clustering analysis: {ENABLE_CLUSTERING}")
            print(f"  - Combined evidence: {ENABLE_COMBINED_EVIDENCE}")
            print(f"  - Adaptive alpha: {ENABLE_ADAPTIVE_ALPHA}")
            print(f"  - Multiple corrections: {ENABLE_MULTIPLE_CORRECTIONS}")
            
            setup_kuznyechik_precomputation_tables()

            # ==================================================================
            #                   MAIN EXPERIMENT PARAMETERS
            # ==================================================================
            NUM_ROUNDS_TO_TEST = 8 
            NUMBER_OF_TRIALS = 5 * (10**6) 
            BLOCK_BIT_LENGTH = 128
            # ==================================================================

            # --- ENHANCED DYNAMIC THRESHOLDS ---
            global STRONG_DIFFERENTIAL_THRESHOLD, MAX_BIAS_THRESHOLD, MIN_OCCURRENCES_THRESHOLD
            if NUM_ROUNDS_TO_TEST >= 9:
                STRONG_DIFFERENTIAL_THRESHOLD = 1  # Alert on even 1 significant pair
                MAX_BIAS_THRESHOLD = 1.2  # Lower threshold for 9 rounds
                MIN_OCCURRENCES_THRESHOLD = 1  # Lower minimum occurrences
            elif NUM_ROUNDS_TO_TEST >= 7:
                STRONG_DIFFERENTIAL_THRESHOLD = 2
                MAX_BIAS_THRESHOLD = 1.4
                MIN_OCCURRENCES_THRESHOLD = 3
            else: 
                STRONG_DIFFERENTIAL_THRESHOLD = 4
                MAX_BIAS_THRESHOLD = 2.4
                MIN_OCCURRENCES_THRESHOLD = 4
            
            print("\nPerforming Optimized Kuznyechik Key Expansion...")
            key_expansion_kuznyechik_optimized(MASTER_KEY_INT_kuznyechik)
            if not validate_implementation():
                sys.exit("Critical validation failed. Aborting.")

            c_values_to_test_raw = get_focused_c_values_noteworthy()
            mask_configurations_full = generate_mask_configs_noteworthy(num_nibbles=BLOCK_BIT_LENGTH // 4)

            parsed_noteworthy_configs = []
            for c_val_int, input_mask, output_mask, config_desc in mask_configurations_full:
                 if c_val_int in c_values_to_test_raw:
                     parsed_noteworthy_configs.append((c_val_int, input_mask, output_mask, config_desc))
            
            configs_to_run = sorted(list(set(parsed_noteworthy_configs)), key=lambda x: (x[0], x[3]))
            total_configs = len(configs_to_run)

            # Dynamic alpha level info
            dynamic_alpha = 0.05 if NUM_ROUNDS_TO_TEST >= 9 else (0.01 if NUM_ROUNDS_TO_TEST >= 7 else 0.005)
            
            print(f"\nAnalysis Parameters (Enhanced Sensitivity for High Rounds):\n  - Rounds: {NUM_ROUNDS_TO_TEST}, Trials/config: {NUMBER_OF_TRIALS:,}\n"
                  f"  - Total configs: {total_configs}, Alert thresholds: >{STRONG_DIFFERENTIAL_THRESHOLD} sig. pairs or >{MAX_BIAS_THRESHOLD:.1f}x bias")
            print(f"  - FDR Alpha (dynamic): {dynamic_alpha:.3e} (more permissive for {NUM_ROUNDS_TO_TEST} rounds)")
            print(f"  - Min occurrences: {MIN_OCCURRENCES_THRESHOLD}")
            print(f"  - GoF Anomaly Alpha: {GOF_ANOMALY_THRESHOLD:.3e}")
            
            results_summary = []
            start_time = time.time()

            for i, (c_val, input_mask, output_mask, config_desc) in enumerate(configs_to_run):
                    current_config_num = i + 1
                    # This line calculates the ETA
                    eta_str = f"ETA: {(time.time() - start_time) / (current_config_num - 1) * (total_configs - current_config_num + 1) / 60:.1f} min" if current_config_num > 1 else ""
                    
                    # The ETA is inserted into this print statement
                    print(f"\n--- Running Config {current_config_num}/{total_configs} {eta_str} ---")
                    print(f"  c = {c_val:#02x}, {config_desc}")
                    sys.stdout.flush()

                    # Enable sequential testing for most promising configurations
                    enable_seq = (c_val in [0xe1, 0x01, 0x03, 0x91, 0xbe]) and (current_config_num <= 10)
                    
                    analysis_result = enhanced_truncated_c_differential_analysis(
                        c_val, input_mask, output_mask, config_desc,
                        NUM_ROUNDS_TO_TEST, NUMBER_OF_TRIALS, BLOCK_BIT_LENGTH,
                        enable_sequential=enable_seq)
                    
                    print_detailed_statistical_report(
                        analysis_result['statistical_results'], 
                        analysis_result['distribution_properties'],
                        analysis_result['gof_results'],
                        analysis_result['config_desc'], 
                        analysis_result['c_val'], 
                        analysis_result['alpha_level_used'],
                        analysis_result['uncorrected_significant'],
                        NUM_ROUNDS_TO_TEST,
                        analysis_result.get('enhanced_metrics'),
                        analysis_result.get('cluster_results'),
                        analysis_result.get('combined_evidence'))
                    
                    # Check all anomaly types
                    check_gof_anomaly(analysis_result['gof_results'], 
                                      analysis_result['config_desc'], 
                                      analysis_result['c_val'], 
                                      NUM_ROUNDS_TO_TEST)
                    
                    # Check combined significance (already enhanced)
                    check_combined_significance(analysis_result['statistical_results'],
                                              NUM_ROUNDS_TO_TEST,
                                              analysis_result['config_desc'],
                                              analysis_result['c_val'])
                    
                    # Check bias persistence
                    max_bias = max([r['bias_ratio'] for r in analysis_result['statistical_results']] or [0.0])
                    check_bias_persistence_anomaly(max_bias, NUM_ROUNDS_TO_TEST, 
                                                 analysis_result['config_desc'], 
                                                 analysis_result['c_val'])

                    check_early_termination(
                        analysis_result['statistical_results'], 
                        analysis_result['config_desc'], 
                        analysis_result['c_val'], 
                        NUM_ROUNDS_TO_TEST,
                        analysis_result.get('combined_evidence'))
                    
                    num_significant = len([r for r in analysis_result['statistical_results'] if r['is_significant_corrected']])
                    num_uncorrected = len(analysis_result['uncorrected_significant'])
                    top_res = analysis_result['statistical_results'][0] if num_significant > 0 else {}
                    
                    # Check for combined evidence significance
                    has_combined_evidence = False
                    if analysis_result.get('combined_evidence'):
                        has_combined_evidence = any(ev['combined_p'] < 0.01 for ev in analysis_result['combined_evidence'].values())
                    
                    results_summary.append({
                        'c_val': c_val, 
                        'config_desc': config_desc, 
                        'num_significant': num_significant,
                        'num_uncorrected': num_uncorrected,
                        'min_corr_p': min([r['corrected_p_value'] for r in analysis_result['statistical_results']] or [1.0]),
                        'top_a': top_res.get('a_val', 'N/A'), 
                        'top_b': top_res.get('b_val', 'N/A'),
                        'max_bias': max_bias,
                        'has_combined_evidence': has_combined_evidence,
                        'sequential_discovery': bool(analysis_result.get('sequential_results') and analysis_result.get('sequential_results').get('discoveries'))
                    })
                    sys.stdout.flush()

            print(f"\n\nAnalysis complete in {time.time() - start_time:.2f} seconds.")
            print("\n\n" + "="*200 + "\nSUMMARY OF ENHANCED SENSITIVITY FINDINGS\n" + "="*200)
            
            # Enhanced summary with multiple criteria
            noteworthy_results = sorted([r for r in results_summary if 
                                       r['num_significant'] > 0 or 
                                       r['max_bias'] >= MAX_BIAS_THRESHOLD or
                                       r['num_uncorrected'] >= 3 or
                                       r['has_combined_evidence'] or
                                       r['sequential_discovery']], 
                                      key=lambda x: x['min_corr_p'])
            
            if not noteworthy_results:
                print("No configurations produced noteworthy results.")
            else:
                print(f"Found {len(noteworthy_results)} configurations with noteworthy results:")
                print(f"{'c':<6} {'Config Description':<30} {'Max Bias':<10} {'FDR Sig':<10} {'Raw Sig':<10} {'Min FDR P':<15} {'Comb.Ev':<8} {'Seq.Disc':<9} {'Top Input (A)':<35} {'Top Output (B)':<35}")
                print("-" * 230)

                for res in noteworthy_results:
                    top_a_str = f"{res['top_a']:#034x}" if isinstance(res['top_a'], int) else 'N/A'
                    top_b_str = f"{res['top_b']:#034x}" if isinstance(res['top_b'], int) else 'N/A'
                    max_bias_str = "inf x" if res['max_bias'] == float('inf') else f"{res['max_bias']:.1f}x"
                    
                    # Enhanced markers
                    marker = ""
                    if res['num_significant'] > 0:
                        marker = "**"  # FDR significant
                    elif res['has_combined_evidence']:
                        marker = "†"   # Combined evidence significant
                    elif res['sequential_discovery']:
                        marker = "§"   # Sequential discovery
                    elif res['num_uncorrected'] >= 5:
                        marker = "*"   # Many uncorrected significant
                    
                    comb_ev = "Yes" if res['has_combined_evidence'] else "No"
                    seq_disc = "Yes" if res['sequential_discovery'] else "No"
                    
                    print(f"{marker}{res['c_val']:#04x}  {res['config_desc']:<30} {max_bias_str:<10} {res['num_significant']:<10} {res['num_uncorrected']:<10} {res['min_corr_p']:<15.2e} {comb_ev:<8} {seq_disc:<9} {top_a_str:<35} {top_b_str:<35}")
                
                print("\nLegend: ** = FDR-significant, † = Combined evidence, § = Sequential discovery, * = 5+ uncorrected significant")

    except Exception as e:
        sys.stdout = original_stdout
        print(f"\n\nAn unexpected error occurred: {e}")
        traceback.print_exc()
    finally:
        sys.stdout = original_stdout
        print(f"\nAnalysis finished. Results saved to {output_filename}")

if __name__ == "__main__":
    try:
        mp.set_start_method('spawn', force=True)
    except RuntimeError:
        pass
    run_kuznyechik_analysis()