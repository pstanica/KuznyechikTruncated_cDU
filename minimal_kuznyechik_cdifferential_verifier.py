#!/usr/bin/env python3
"""
Minimal deterministic verifier for the masked inner c-differential
experiment on Kuznyechik without initial key whitening.

This script is intentionally small compared with the exploratory search code:
  * no SageMath;
  * no multiprocessing;
  * no adaptive thresholds;
  * no clustering or sequential testing;
  * fixed PRNG seed by default;
  * one selected candidate pair (a,b) is verified directly.

Default parameters reproduce the reported 9-round configuration
    c = 0x04, byte_8_in -> byte_8_out,
    a = 0x29 in byte 8, b = 0x8d in byte 8,
for the no-initial-whitening Kuznyechik round core.

Byte numbering in command-line parameters is 1-based from the left/MSB:
byte 1 is the most significant byte and byte 16 is the least significant byte.

Run it with something like:

python3 minimal_kuznyechik_cdifferential_verifier.py \
  --rounds 9 \
  --c 0x04 \
  --input-byte 8 \
  --output-byte 8 \
  --a 29 \
  --b 8d \
  --seed 42 \
  --trials 100000

  (perhaps change to 5000000 to be more accurate in the statistics)
"""

from __future__ import annotations

import argparse
import math
import random
import time
from typing import List, Sequence, Tuple

# Kuznyechik S-box pi from GOST R 34.12-2015 / RFC 7801.
SBOX = [
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
    89, 166, 116, 210, 230, 244, 180, 192, 209, 102, 175, 194, 57, 75, 99, 182,
]

# Coefficients of the Kuznyechik l-function.
L_VEC = [148, 32, 133, 16, 194, 192, 1, 251, 1, 192, 194, 16, 133, 32, 148, 1]

# GF(2^8) modulus x^8 + x^7 + x^6 + x + 1.
# In the usual integer representation this is 0x1C3, and reduction after
# overflow uses the low byte 0xC3.
RED_POLY_LOW = 0xC3


def gf_mul(a: int, b: int) -> int:
    """Multiply two bytes in GF(2^8) modulo x^8+x^7+x^6+x+1."""
    res = 0
    for _ in range(8):
        if b & 1:
            res ^= a
        carry = a & 0x80
        a = (a << 1) & 0xFF
        if carry:
            a ^= RED_POLY_LOW
        b >>= 1
    return res


GF_MUL = [[gf_mul(a, b) for b in range(256)] for a in range(256)]


def xor_blocks(a: Sequence[int], b: Sequence[int]) -> List[int]:
    return [x ^ y for x, y in zip(a, b)]


def int_to_block(x: int) -> List[int]:
    return [(x >> (8 * (15 - i))) & 0xFF for i in range(16)]


def block_to_int(block: Sequence[int]) -> int:
    x = 0
    for byte in block:
        x = (x << 8) | (byte & 0xFF)
    return x


def r_transform(state: Sequence[int]) -> List[int]:
    z = 0
    for coeff, byte in zip(L_VEC, state):
        z ^= GF_MUL[coeff][byte]
    return [z] + list(state[:15])


def l_transform(state: Sequence[int]) -> List[int]:
    out = list(state)
    for _ in range(16):
        out = r_transform(out)
    return out


def s_transform(state: Sequence[int]) -> List[int]:
    return [SBOX[b] for b in state]


def round_constants() -> List[List[int]]:
    constants = [[0] * 16]
    for i in range(1, 33):
        constants.append(l_transform([0] * 15 + [i]))
    return constants


C = round_constants()


def key_schedule(master_key: int) -> List[List[int]]:
    """Return the ten 128-bit round keys K_0,...,K_9 as byte lists."""
    k1 = int_to_block(master_key >> 128)
    k2 = int_to_block(master_key & ((1 << 128) - 1))
    keys = [k1[:], k2[:]]
    left, right = k1, k2
    for i in range(4):
        for j in range(1, 9):
            c_j = C[8 * i + j]
            t = xor_blocks(left, c_j)
            t = s_transform(t)
            t = l_transform(t)
            t = xor_blocks(t, right)
            left, right = t, left
        keys.extend([left[:], right[:]])
    return keys


def encrypt_standard(block: Sequence[int], keys: Sequence[Sequence[int]], rounds: int = 9) -> List[int]:
    """Standard Kuznyechik core with initial whitening, for RFC validation."""
    state = xor_blocks(block, keys[0])
    for r in range(1, rounds + 1):
        state = s_transform(state)
        state = l_transform(state)
        state = xor_blocks(state, keys[r])
    return state


def encrypt_no_initial_whitening(block: Sequence[int], keys: Sequence[Sequence[int]], rounds: int) -> List[int]:
    """No-pre-whitening round core R_{K_rounds} o ... o R_{K_1}."""
    state = list(block)
    for r in range(1, rounds + 1):
        state = s_transform(state)
        state = l_transform(state)
        state = xor_blocks(state, keys[r])
    return state


def validate_against_rfc7801() -> None:
    master_key = 0x8899AABBCCDDEEFF0011223344556677FEDCBA98765432100123456789ABCDEF
    plaintext = 0x1122334455667700FFEEDDCCBBAA9988
    expected_ciphertext = 0x7F679D90BEBC24305A468D42B9D4EDCD
    expected_keys = [
        0x8899AABBCCDDEEFF0011223344556677,
        0xFEDCBA98765432100123456789ABCDEF,
        0xDB31485315694343228D6AEF8CC78C44,
        0x3D4553D8E9CFEC6815EBADC40A9FFD04,
        0x57646468C44A5E28D3E59246F429F1AC,
        0xBD079435165C6432B532E82834DA581B,
        0x51E640757E8745DE705727265A0098B1,
        0x5A7925017B9FDD3ED72A91A22286F984,
        0xBB44E25378C73123A5F32F73CDB6E517,
        0x72E9DD7416BCF45B755DBAA88E4A4043,
    ]
    keys = key_schedule(master_key)
    got_keys = [block_to_int(k) for k in keys]
    if got_keys != expected_keys:
        raise RuntimeError("Kuznyechik key schedule does not match RFC 7801 test vectors")
    got = block_to_int(encrypt_standard(int_to_block(plaintext), keys, 9))
    if got != expected_ciphertext:
        raise RuntimeError(
            f"Kuznyechik encryption does not match RFC 7801: got {got:032x}, expected {expected_ciphertext:032x}"
        )


def byte_value_to_block(value: int, byte_number: int) -> List[int]:
    """Put value in a 1-based MSB byte position; all other bytes are zero."""
    if not (1 <= byte_number <= 16):
        raise ValueError("byte_number must be in {1,...,16}")
    block = [0] * 16
    block[byte_number - 1] = value & 0xFF
    return block


def parse_candidate(value: str, byte_number: int) -> List[int]:
    """Parse either a full 128-bit hex value or a one-byte value."""
    s = value.lower().removeprefix("0x")
    x = int(s, 16)
    if x < 0 or x >= (1 << 128):
        raise ValueError("candidate value must fit in 128 bits")
    if len(s) <= 2:
        return byte_value_to_block(x, byte_number)
    return int_to_block(x)


def multiply_state_by_c(c: int, state: Sequence[int]) -> List[int]:
    return [GF_MUL[c][b] for b in state]


def normal_approx_two_sided_p(observed: int, trials: int, p: float) -> float:
    """Two-sided binomial p-value using a normal approximation with continuity correction."""
    mu = trials * p
    var = trials * p * (1.0 - p)
    if var <= 0:
        return 0.0 if observed != round(mu) else 1.0
    # Continuity correction away from the mean.
    diff = abs(observed - mu) - 0.5
    z = max(0.0, diff / math.sqrt(var))
    return math.erfc(z / math.sqrt(2.0))


def masked_byte(block: Sequence[int], byte_number: int) -> int:
    return block[byte_number - 1]


def verify(args: argparse.Namespace) -> None:
    validate_against_rfc7801()

    master_key = int(args.key, 16)
    keys = key_schedule(master_key)
    rng = random.Random(args.seed)

    a_block = parse_candidate(args.a, args.input_byte)
    b_block = parse_candidate(args.b, args.output_byte)
    target_a_byte = masked_byte(a_block, args.input_byte)
    target_b_byte = masked_byte(b_block, args.output_byte)
    if target_a_byte == 0:
        raise ValueError("the selected input byte of a must be nonzero")

    total_nonzero = 0
    observed = 0
    start = time.time()

    for _ in range(args.trials):
        x_int = rng.getrandbits(128)
        x = int_to_block(x_int)

        # The minimal verifier fixes the candidate masked input difference a.
        # Thus x' = c*x + a componentwise over GF(2^8), with XOR addition.
        cx = multiply_state_by_c(args.c, x)
        x_prime = xor_blocks(cx, a_block)

        y = encrypt_no_initial_whitening(x, keys, args.rounds)
        y_prime = encrypt_no_initial_whitening(x_prime, keys, args.rounds)

        dy = xor_blocks(y, y_prime)  # full XOR output difference first
        out_byte = masked_byte(dy, args.output_byte)  # mask/project only afterward

        total_nonzero += 1
        if out_byte == target_b_byte:
            observed += 1

    elapsed = time.time() - start

    # With a fixed nonzero one-byte input a, the null distribution for the selected
    # output byte is uniform over 2^8 possible byte values.
    expected_prob = 1.0 / 256.0
    expected_count = total_nonzero * expected_prob
    bias_ratio = observed / expected_count if expected_count > 0 else float("nan")
    p_value = normal_approx_two_sided_p(observed, total_nonzero, expected_prob)

    print("Minimal masked inner c-differential verifier")
    print("Kuznyechik implementation: RFC 7801 key schedule/encryption test passed")
    print(f"model                       : no initial key whitening")
    print(f"rounds                      : {args.rounds}")
    print(f"master key                  : 0x{master_key:064x}")
    print(f"c                           : 0x{args.c:02x}")
    print(f"input byte / output byte    : {args.input_byte} -> {args.output_byte} (1-based, MSB first)")
    print(f"a                           : 0x{block_to_int(a_block):032x}")
    print(f"b                           : 0x{block_to_int(b_block):032x}")
    print(f"seed                        : {args.seed}")
    print(f"trials                      : {args.trials:,}")
    print(f"elapsed seconds             : {elapsed:.2f}")
    print(f"observed count              : {observed:,}")
    print(f"random-baseline expectation : {expected_count:.3f}")
    print(f"bias ratio                  : {bias_ratio:.6g} x")
    print(f"two-sided binomial p-value  : {p_value:.6g}  (normal approximation)")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Minimal deterministic verifier for one masked inner c-differential candidate."
    )
    parser.add_argument("--key", default="8899aabbccddeeff0011223344556677fedcba98765432100123456789abcdef")
    parser.add_argument("--rounds", type=int, default=9)
    parser.add_argument("--c", type=lambda s: int(s, 0), default=0x04)
    parser.add_argument("--input-byte", type=int, default=8, help="1-based byte index from left/MSB")
    parser.add_argument("--output-byte", type=int, default=8, help="1-based byte index from left/MSB")
    parser.add_argument("--a", default="29", help="one-byte hex value or full 128-bit hex value")
    parser.add_argument("--b", default="8d", help="one-byte hex value or full 128-bit hex value")
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--trials", type=int, default=100000, help="use e.g. 5000000 for the reported scale")
    args = parser.parse_args()

    if not (1 <= args.rounds <= 9):
        raise ValueError("rounds must be between 1 and 9")
    if not (0 <= args.c <= 255):
        raise ValueError("c must be a byte")
    verify(args)


if __name__ == "__main__":
    main()
