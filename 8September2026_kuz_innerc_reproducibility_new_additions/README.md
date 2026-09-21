# Kuznyechik inner-c reproducibility package

This package contains the programs, generated tables, certificates, and execution records for the structural inner-c analysis and the two-round standard-Kuznyechik key-recovery experiment.

## Contents

- `source/kuz_innerc_repro_v2.py`: inner tables, multiplier spectrum, Perrin transfer, disagreement ranks, energy tables, weak-key results, exact two-round channels, and Stage-1 recovery.
- `source/full_master_key_recovery_v3.py`: two-stage recovery of the 256-bit master key for two-round standard Kuznyechik.
- `source/verify_additional_certificates.py`: determinant, row-distinctness, spectral, rank-degree, and random-key Stage-2 checks.
- `outputs/`: machine-readable results generated on the recorded macOS system.
- `logs/`: captured standard output and execution times.
- `environment.txt`: tested software versions.
- `SHA256SUMS.txt`: SHA-256 checksums for the package files.

Run the commands below from the package root.

## Two-round master-key recovery

```bash
python3 source/full_master_key_recovery_v3.py \
    --c 0x04 \
    --error 0.01 \
    --out reproduced_results_v3.json
```

## Additional exact and numerical certificates

```bash
python3 source/verify_additional_certificates.py \
    --out reproduced_additional_certificates \
    --c 0x04 \
    --random-key-trials 100 \
    --stage2-samples 40 \
    --seed 20260906
```

## Complete structural computation

```bash
python3 source/kuz_innerc_repro_v2.py \
    --out reproduced_core_results \
    --extended-outputs \
    --mc 200000 \
    --key-demo 14117 \
    --key-c 0x04 \
    --full-c-key-search
```

The required dependencies are Python 3 and NumPy. SciPy is used for the exact-binomial power table. The versions used for the recorded run are listed in `environment.txt`.

The principal recorded result uses `c=0x04`, a total error target of `0.01`, and stage budgets of `0.005`. It recovers the complete 256-bit RFC test master key using 226,512 chosen-plaintext pairs, corresponding to 240,669 distinct encryption queries. The additional regression test recovers the second master-key half for 100 out of 100 independently generated master keys.

Small final-digit differences in floating-point values can occur across NumPy or SciPy versions. Rows tied under the reported objective may also appear in a different order. The exact integer certificates and substantive numerical conclusions are unaffected.
