#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""Standalone quickstart demonstration across Pillars I, II, and III."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "python"))

from triad_verify.complexity_triad import run_all_triad_checks  # noqa: E402
from triad_verify.mlwe_tightness import run_all_mlwe_checks  # noqa: E402
from triad_verify.pir_koszul import (  # noqa: E402
    koszul_rate_exact,
    lfsr_rate_exact,
    verify_certified_f11_byzantine,
    verify_koszul_rank_grid,
)


def main() -> int:
    print("=== coded-pir-mlwe-complexity-lab Quickstart Demo ===")

    # Pillar I: CS-053
    r_kv = koszul_rate_exact(6, 3, 3)
    r_lfsr = lfsr_rate_exact(6, 3, 3)
    r_lfsr_str = str(r_lfsr) if r_lfsr is not None else "Infeasible (E=6 < KT=9; Ex. VII.A prior = 4/7)"
    grid = verify_koszul_rank_grid()
    f11 = verify_certified_f11_byzantine(ROOT / "data" / "f11_byz_witness.json")
    print(f"[Pillar I | CS-053] Koszul-Veronese (6,3,3) rate = {r_kv} vs LFSR: {r_lfsr_str}")
    print(
        f"[Pillar I | CS-053] Koszul rank grid verified: {grid['checked_blocks']} blocks "
        f"({grid['strict_savings_count']} with strict savings)"
    )
    print(f"[Pillar I | CS-053] F_11 Byzantine rate-2/5 witness: {f11}")

    # Pillar II: CS-026
    mlwe = run_all_mlwe_checks()
    renyi = mlwe["renyi_60digit"]
    print(
        f"[Pillar II | CS-026] ML-KEM Renyi-2 cliff: "
        f"CBD2 min R2={renyi['CBD_2']['min_r2']} (1024-bit loss={renyi['CBD_2']['cumulative_bits_r2']['2048']} bits) vs "
        f"CBD3 min R2={renyi['CBD_3']['min_r2']} (512-bit loss={renyi['CBD_3']['cumulative_bits_r2']['1024']} bits), "
        f"ratio={renyi['cliff_ratio_1024_over_512']}x"
    )
    print(
        f"[Pillar II | CS-026] Chen Step-9 all even modes vanish: {mlwe['chen_step9']['all_even_modes_vanish']} | "
        f"Luo det ideal across 10 secrets: {mlwe['luo_det_ideal']['observed_abs_dets_across_10_secrets']}"
    )
    qgtl = mlwe["qgtl_berry_curvature"]
    print(
        f"[Pillar II | CS-026] QGTL Berry curvature: e0=0 -> {qgtl['symmetric_e0_0']['omega_ts']:.3e}, "
        f"e0=+0.35 -> {qgtl['biased_e0_pos035']['omega_ts']:.6f}"
    )
    if "dyadic256_60digit" in mlwe:
        dy = mlwe["dyadic256_60digit"]
        cbd2_bits = float(renyi["CBD_2"]["cumulative_bits_r2"]["2048"])
        dy_bits = float(dy["loss_bits_1024"])
        print(
            f"[Pillar II | T2e] Dyadic-256 (Var=1, 1-byte CT): min R2={dy['min_r2']} "
            f"(1024-bit loss={dy_bits:.3f} bits, {cbd2_bits / dy_bits:.2f}x drop vs CBD_2)"
        )

    # Pillar III: CS-001 / CS-004 / CS-012 / CS-051 / CS-026 <-> CS-053
    triad = run_all_triad_checks()
    kt_info = ""
    if "koszul_flattening_tensor_rank" in triad:
        kt = triad["koszul_flattening_tensor_rank"]
        kt_info = (
            f" | Koszul tensor rank: M2>={kt['M2_rank_lower_bound_every_field']} "
            f"({kt['M2_left_inverse_nnz']}-nnz Z-inv) & "
            f"T3>={kt['T3_rank_lower_bound_every_field']} (all fields incl. char 2)"
        )
    print(
        f"[Pillar III | Triad] Algebrization MLE points={triad['algebrization_mle']['points_multilinearity_verified']} | "
        f"LDC min distance={triad['katz_trevisan_ldc']['min_hamming_distance']} >= 3 | "
        f"Compress_1 margin={triad['mlwe_compress1_ceiling']['exact_safe_margin']} (first fail={triad['mlwe_compress1_ceiling']['first_failure']})"
        f"{kt_info}"
    )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
