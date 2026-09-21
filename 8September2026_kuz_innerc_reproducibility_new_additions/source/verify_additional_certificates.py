#!/usr/bin/env python3
"""Generate the determinant, row-distinctness, spectral, and Stage-2 certificates."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

import numpy as np

import full_master_key_recovery_v3 as recovery
import kuz_innerc_repro_v2 as core


def determinant_mod_prime(matrix: np.ndarray, prime: int) -> int:
    """Return the determinant modulo a prime using exact elimination."""
    a = np.asarray(matrix, dtype=np.int64).copy() % prime
    n = a.shape[0]
    if a.shape != (n, n):
        raise ValueError("matrix must be square")

    determinant = 1
    for column in range(n):
        pivot = next(
            (row for row in range(column, n) if int(a[row, column]) != 0),
            None,
        )
        if pivot is None:
            return 0
        if pivot != column:
            a[[column, pivot]] = a[[pivot, column]]
            determinant = -determinant

        pivot_value = int(a[column, column])
        determinant = determinant * pivot_value % prime
        pivot_inverse = pow(pivot_value, -1, prime)
        a[column, column:] = (
            a[column, column:] * pivot_inverse
        ) % prime

        for row in range(column + 1, n):
            factor = int(a[row, column])
            if factor:
                a[row, column:] = (
                    a[row, column:] - factor * a[column, column:]
                ) % prime

    return determinant % prime


def spectral_certificate() -> dict:
    """Compute the restricted norm on the nonzero-difference zero-sum subspace."""
    w_star = core.DDT[1:, 1:].astype(np.float64) / 256.0
    size = w_star.shape[0]
    projector = np.eye(size) - np.full((size, size), 1.0 / size)
    restricted = projector @ w_star @ projector
    sigma_perp = float(np.linalg.svd(restricted, compute_uv=False)[0])

    assert np.allclose(w_star.sum(axis=0), 1.0)
    assert np.allclose(w_star.sum(axis=1), 1.0)
    assert abs(sigma_perp - 0.21027588246191825) < 1e-12

    return {
        "method": "largest singular value of P W_* P, where P projects onto the zero-sum subspace",
        "sigma_perp": sigma_perp,
        "sigma_perp_squared": sigma_perp * sigma_perp,
    }


def row_distinctness_certificate(output: Path) -> dict:
    """Check all nonzero multipliers and write one exact result per multiplier."""
    rows = []
    failures = []
    rank_failures = []

    for c in range(1, 256):
        inner = core.inner_table(c)
        unique_rows = int(np.unique(inner, axis=0).shape[0])
        rank = core.disagreement_rank(c, c)
        degree = c.bit_length() - 1
        row = {
            "c": f"0x{c:02x}",
            "unique_rows": unique_rows,
            "pairwise_distinct": unique_rows == 256,
            "disagreement_rank": rank,
            "representative_degree": degree,
            "rank_equals_degree": rank == degree,
        }
        rows.append(row)
        if unique_rows != 256:
            failures.append(f"0x{c:02x}")
        if rank != degree:
            rank_failures.append(f"0x{c:02x}")

    with output.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    assert not failures
    assert not rank_failures
    return {
        "multipliers_checked": len(rows),
        "all_inner_tables_have_256_pairwise_distinct_rows": True,
        "all_same_representative_disagreement_ranks_equal_degree": True,
        "output_file": output.name,
    }


def random_key_stage2_certificate(
    output: Path,
    trials: int,
    samples: int,
    c: int,
    seed: int,
) -> dict:
    """Repeat Stage 2 for deterministic independently generated master keys."""
    rng = np.random.default_rng(seed)
    rows = []

    for trial in range(trials):
        master = rng.integers(0, 256, size=32, dtype=np.uint8).tobytes()
        keys = core.standard_round_keys(master)
        result = recovery.recover_second_half(
            c,
            samples,
            keys[0].copy(),
            keys,
            seed=seed + trial + 1,
        )
        rows.append(
            {
                "trial": trial + 1,
                "success": bool(result["success"]),
                "true_second_master_half": result["true_second_master_half"],
                "recovered_second_master_half": result[
                    "recovered_second_master_half"
                ],
            }
        )

    with output.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    successes = sum(int(row["success"]) for row in rows)
    assert successes == trials
    return {
        "multiplier": f"0x{c:02x}",
        "samples_per_byte": samples,
        "seed": seed,
        "trials": trials,
        "successes": successes,
        "failures": trials - successes,
        "output_file": output.name,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default="additional_certificates")
    parser.add_argument("--c", type=lambda value: int(value, 0), default=0x04)
    parser.add_argument("--random-key-trials", type=int, default=100)
    parser.add_argument("--stage2-samples", type=int, default=40)
    parser.add_argument("--seed", type=int, default=20260906)
    args = parser.parse_args()

    if args.c in (0, 1):
        raise ValueError("c must be different from 0 and 1")
    if args.random_key_trials < 1 or args.stage2_samples < 1:
        raise ValueError("trial and sample counts must be positive")

    output_directory = Path(args.out)
    output_directory.mkdir(parents=True, exist_ok=True)

    core.rfc_regression_tests()
    determinant = determinant_mod_prime(core.DDT[1:, 1:], 5)
    assert determinant == 1

    result = {
        "rfc_7801_regression_tests": "PASS",
        "nonzero_ddt_block": {
            "dimension": 255,
            "modulus": 5,
            "determinant_modulo_prime": determinant,
            "nonsingular": determinant != 0,
        },
        "row_distinctness_and_rank": row_distinctness_certificate(
            output_directory / "inner_table_row_distinctness.csv"
        ),
        "spectral": spectral_certificate(),
        "random_key_stage2": random_key_stage2_certificate(
            output_directory / "random_key_stage2_trials.csv",
            args.random_key_trials,
            args.stage2_samples,
            args.c,
            args.seed,
        ),
    }

    summary_path = output_directory / "additional_certificates.json"
    summary_path.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n")
    print(json.dumps(result, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
