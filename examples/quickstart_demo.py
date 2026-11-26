#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""Standalone quickstart demonstration across Pillars I, II, and III."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "python"))

from triad_verify.complexity_triad import run_all_triad_checks
from triad_verify.mlwe_tightness import run_all_mlwe_checks
from triad_verify.pir_koszul import (
    koszul_rate_exact,
    lfsr_rate_exact,
    verify_certified_f11_byzantine,
    verify_koszul_rank_grid,
)
from triad_verify.polymatroid_barrier import verify_6obj_f2_64_realization


def main() -> int:
    print("=== coded-pir-mlwe-complexity-lab v5.0.0 Quickstart Demo ===")

    # Pillar I: CS-053
    r_kv = koszul_rate_exact(6, 3, 3)
    r_lfsr = lfsr_rate_exact(6, 3, 3)
    r_lfsr_str = str(r_lfsr) if r_lfsr is not None else "Infeasible (E=6 < KT=9; Ex. VII.A prior = 4/7)"
    grid = verify_koszul_rank_grid()
    f11 = verify_certified_f11_byzantine(ROOT / "data" / "f11_byz_witness.json")
    t1j = verify_6obj_f2_64_realization(ROOT / "data" / "h_uncond_certified.json")
    print(f"[Pillar I | CS-053] Koszul-Veronese (6,3,3) rate = {r_kv} vs LFSR: {r_lfsr_str}")
    print(
        f"[Pillar I | CS-053] Koszul rank grid verified: {grid['checked_blocks']} blocks "
        f"({grid['strict_savings_count']} with strict savings)"
    )
    print(f"[Pillar I | CS-053] F_11 Byzantine rate-2/5 witness: {f11}")
    print(
        f"[Pillar I | T1j] Single Z_4-cyclic F_2^64 6-subspace realization: "
        f"{t1j['subsets_exact_match']}/64 subsets matched at scale 4"
    )

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
    dy = mlwe["dyadic256_60digit"]
    cbd2_bits = float(renyi["CBD_2"]["cumulative_bits_r2"]["2048"])
    dy_bits = float(dy["loss_bits_1024"])
    print(
        f"[Pillar II | T2e] Dyadic-256 (Var=1, 1-byte CT): min R2={dy['min_r2']} "
        f"(1024-bit loss={dy_bits:.3f} bits, {cbd2_bits / dy_bits:.2f}x drop vs CBD_2)"
    )
    d5 = mlwe["dyadic512_dfr_variational"]
    cbd3_bits = float(renyi["CBD_3"]["cumulative_bits_r2"]["1024"])
    d5_bits = float(d5["loss_bits_512"])
    dfrs = d5["exact_dfr_suite"]
    print(
        f"[Pillar II | T2g] Dyadic-512 (Var=3/2, kappa_ex=0, 9-bit CT): min R2={d5['min_r2']} "
        f"(512-bit loss={d5_bits:.3f} bits, {cbd3_bits / d5_bits:.2f}x drop vs CBD_3) | "
        f"Exact DFRs: 512=2^{dfrs['ML_KEM_512_Dyadic512_256']['union_bound_log2_dfr']}, "
        f"768=2^{dfrs['ML_KEM_768_Dyadic256']['union_bound_log2_dfr']}, "
        f"1024=2^{dfrs['ML_KEM_1024_Dyadic256']['union_bound_log2_dfr']}"
    )
    d10 = mlwe["dyadic1024_bai_and_all_order"]
    bai = d10["bai_overhead_suite"]
    print(
        f"[Pillar II | T2h] 10-bit CT Dyadic-1024-A/B Bai et al. (2018) collapse: "
        f"ML-KEM-1024 {bai['ML_KEM_1024_CBD2']['bai_overhead_bits']:.2f}b -> "
        f"{bai['ML_KEM_1024_Dyadic1024A']['bai_overhead_bits']:.2f}b, "
        f"ML-KEM-512 {bai['ML_KEM_512_CBD3']['bai_overhead_bits']:.2f}b -> "
        f"{bai['ML_KEM_512_Dyadic1024B']['bai_overhead_bits']:.2f}b"
    )
    d16 = mlwe["dyadic16384_gaussian_paradox"]
    bai16 = d16["bai_16384_suite"]
    gp = d16["gaussian_dfr_paradox"]
    print(
        f"[Pillar II | T2i] ML-KEM-1024 Gaussian DFR Paradox: D_sigma=1 FAILS at 2^{gp['mlkem_1024_gauss_log2_dfr']} (> 2^-174), "
        f"while 14-bit Dyadic-16384-A achieves Bai={bai16['ML_KEM_1024_Dyadic16384A']['bai_overhead_bits']:.3f}b "
        f"(DFR 2^{d16['dfr_16384_suite']['ML_KEM_1024_Dyadic16384A']['union_bound_log2_dfr']}) & "
        f"Dyadic-16384-B hits sub-1-bit ML-KEM-512 Bai={bai16['ML_KEM_512_Dyadic16384B']['bai_overhead_bits']:.4f}b!"
    )

    # Pillar III: CS-001 / CS-004 / CS-012 / CS-051 / CS-CMP-012 / CS-026 <-> CS-053
    triad = run_all_triad_checks()
    kt = triad["koszul_flattening_tensor_rank"]
    sw = triad["strassen_and_all_m_koszul"]
    bl = triad["brockett_dobkin_and_lovasz_shannon_capacity"]
    szp = triad["schwartz_zippel_and_paley_family"]
    primes = [item["p"] for item in szp["paley_conference_sos_verified"]]
    print(
        f"[Pillar III | Triad] Algebrization MLE points={triad['algebrization_mle']['points_multilinearity_verified']} | "
        f"LDC min distance={triad['katz_trevisan_ldc']['min_hamming_distance']} >= 3 | "
        f"Compress_1 margin={triad['mlwe_compress1_ceiling']['exact_safe_margin']} | "
        f"Strassen-Winograd rank_F(<2,2,2>)={sw['M2_exact_rank_every_field']} | "
        f"Koszul M2>={kt['M2_rank_lower_bound_every_field']}, T3>={kt['T3_rank_lower_bound_every_field']} | "
        f"Brockett-Dobkin m=3: {bl['brockett_dobkin_m3_vs_koszul']['bd']} > {bl['brockett_dobkin_m3_vs_koszul']['koszul_ceiling']} | "
        f"Paley Z[sqrt(p)] SOS & Theta(P_p)=sqrt(p) verified for p={primes}"
    )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
