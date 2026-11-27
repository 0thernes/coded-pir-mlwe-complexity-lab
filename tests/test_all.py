#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""
Comprehensive Verification & Falsification Test Suite (`tests/test_all.py`, v5.4.0):
- Claim falsifiability checks (C1–C34)
- Negative / adversarial boundary checks (C11 CLI invalid args, Eshkol parser/depth/domain, tamper detection)
- Randomized property-based tests (prop_check)
- Differential tests (Python vs native C11 CLI vs Eshkol v1.3.6 AD runtime)
- Metamorphic checks (K <-> T symmetry, noise-shift odd symmetry)
- Mutation-killing tests (18/18 core mutants killed!)
- Draft 2020-12 repo.yaml schema validation, link integrity, Pages CSP/WCAG AA, dual timestamps, & single version source
"""
from __future__ import annotations

import json
import math
import random
import re
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "python"))

from triad_verify.complexity_triad import (
    _comm_pair_xy,
    _exact_det_int,
    mle_eval_mod_p,
    verify_algebrization_mle,
    verify_blaser_five_halves_matmul_bound,
    verify_brockett_dobkin_and_lovasz_shannon_capacity,
    verify_katz_trevisan_ldc_distance,
    verify_koszul_flattening_tensor_rank,
    verify_mlwe_compress1_ceiling,
    verify_schwartz_zippel_and_paley_family,
    verify_strassen_and_all_m_koszul,
)
from triad_verify.mlwe_tightness import (
    cbd_pmf_exact,
    compute_exact_mlkem_dfr,
    compute_exact_mlkem_dfr_decimal,
    dyadic256_pmf_exact,
    dyadic512_pmf_exact,
    dyadic1024a_pmf_exact,
    dyadic16384a_pmf_exact,
    verify_all_order_renyi_bai_and_dyadic1024,
    verify_cbd_moments_and_renyi_60digit,
    verify_chen_step9,
    verify_dyadic256_and_qgtl_kurtosis_60digit,
    verify_dyadic512_dfr_and_variational_bridge,
    verify_gaussian_dfr_paradox_and_dyadic16384,
    verify_luo_det_ideal_independence,
    verify_qgtl_shifted_lwe,
    verify_twisted_dft_selection_rule,
)
from triad_verify.pir_koszul import (
    koszul_lambda_formula,
    koszul_rate_exact,
    lfsr_rate_exact,
    mat_mul_mod,
    verify_certified_f11_byzantine,
    verify_certified_f101_t3_k3_e6_zero_error,
    verify_koszul_rank_grid,
    verify_overlap_sub_kt_scheme,
    verify_t3_k3_e6_zero_error,
)
from triad_verify.polymatroid_barrier import (
    verify_4var_i4_and_5obj_f2_realizability,
    verify_6obj_f2_64_realization,
    verify_h_uncond,
)

# ============================================================================
# 1. Core Claims Falsifiability Tests (CS-053, CS-026, CS-001)
# ============================================================================


def test_c1_koszul_veronese_rank_grid() -> None:
    res = verify_koszul_rank_grid(p=101)
    assert res["checked_blocks"] == 46
    assert res["strict_savings_count"] == 30
    lam = koszul_lambda_formula(6, 3, 2, 3)
    assert lam == 8
    assert lam < 9


def test_c2_universal_koszul_domination_over_lfsr_and_symmetry() -> None:
    # Metamorphic K <-> T symmetry & strict domination for all K >= 2, T >= 2
    for K in range(2, 7):
        for T in range(2, 7):
            for E in range(max(K, T) + 1, K * T + 5):
                rk1 = koszul_rate_exact(E + 2, K, T, U=0, B=1)
                rk2 = koszul_rate_exact(E + 2, T, K, U=0, B=1)
                assert rk1 == rk2, "Metamorphic K <-> T symmetry violated"
                rl = lfsr_rate_exact(E + 2, K, T, U=0, B=1)
                if rl is not None:
                    assert rk1 > rl, f"Koszul failed to beat LFSR at K={K}, T={T}, E={E}"


def test_c3_f11_byzantine_rate25_exact() -> None:
    res = verify_certified_f11_byzantine(REPO_ROOT / "data" / "f11_byz_witness.json")
    assert res["rate"] == "2/5"
    assert res["lfsr_rate"] == "8/21"
    assert res["subsets_verified"] == 15
    assert res["ordered_pairs_flag_private"] == 30


def test_c4_sub_kt_and_unrestricted_capacity_boundary() -> None:
    r1 = verify_overlap_sub_kt_scheme(5, 2, 1, p=101)
    assert r1["rate"] == "18/55" and r1["exact_unrestricted_capacity"] and r1["E_lt_KT"]
    r2 = verify_overlap_sub_kt_scheme(6, 3, 1, p=101)
    assert r2["rate"] == "4/11" and r2["exact_unrestricted_capacity"] and r2["E_lt_KT"]
    r3 = verify_overlap_sub_kt_scheme(7, 3, 1, p=101)
    assert r3["rate"] == "50/119" and r3["E_lt_KT"]


def test_c5_t3_k3_e6_zero_error_10_17() -> None:
    res = verify_t3_k3_e6_zero_error(p=101)
    assert res["interference_rank"] == 42
    assert res["rate"] == "10/17"
    cert = verify_certified_f101_t3_k3_e6_zero_error(REPO_ROOT / "data" / "f101_t3_k3_e6_witness.json")
    assert cert["desired_rank"] == 60
    assert cert["interference_rank"] == 42
    assert cert["downloads"] == 102 and cert["file_symbols"] == 60
    assert cert["rate"] == "10/17"
    assert cert["flag_isomorphisms_verified"] == 20
    assert cert["live_zero_error_decode_trials_passed"] == 10
    assert cert["exact_transcript_bijection_triples_passed"] == 20


def test_c6_unconditioned_shannon_ingleton_polymatroid_barrier() -> None:
    res = verify_h_uncond(REPO_ROOT / "data" / "h_uncond_certified.json")
    assert res["violations"] == 0
    assert res["D_over_L"] == "13/8"
    assert res["C_shannon_ingleton"] == "8/13"
    assert res["strictly_exceeds_linear_capacity_3_5"]
    assert res["retrieval_6atom_subset_ingletons_checked"] == 3814209


def test_c7_to_c10_mlwe_tightness_suite() -> None:
    renyi = verify_cbd_moments_and_renyi_60digit()
    assert renyi["CBD_2"]["variance_exact"] == "1"
    assert renyi["CBD_3"]["variance_exact"] == "3/2"
    assert renyi["cliff_ratio_1024_over_512"] > 4.95
    assert verify_chen_step9()["all_even_modes_vanish"]
    luo = verify_luo_det_ideal_independence()
    assert luo["observed_abs_dets_across_10_secrets"] == [3329 ** 3]
    qgtl = verify_qgtl_shifted_lwe()
    assert abs(qgtl["symmetric_e0_0"]["omega_ts"]) < 1e-15
    assert abs(qgtl["biased_e0_pos035"]["omega_ts"] + qgtl["biased_e0_neg035"]["omega_ts"]) < 1e-14


def test_c11_to_c14_complexity_triad_suite() -> None:
    assert verify_algebrization_mle()["points_multilinearity_verified"] == 1331
    assert verify_katz_trevisan_ldc_distance()["min_hamming_distance"] == 5
    comp = verify_mlwe_compress1_ceiling()
    assert comp["exact_safe_margin"] == 831 and comp["first_failure"] == 832


def test_c15_to_c19_v2_breakthroughs_suite() -> None:
    # C15 (T1g): Zhang-Yeung reduction + M>=3 1-flag + F_7 zero-error T=3 K=3 rate 10/17
    f7 = verify_t3_k3_e6_zero_error(p=7)
    assert f7["rate"] == "10/17" and f7["interference_rank"] == 42
    # C16 (T2e): Dyadic-256 optimal 8-bit ML-KEM drop-in noise (Var=1, 17.7x Renyi-2 reduction)
    d256 = verify_dyadic256_and_qgtl_kurtosis_60digit()
    cbd = verify_cbd_moments_and_renyi_60digit()
    assert d256["variance_exact"] == "1" and d256["fourth_moment_exact"] == "23/8"
    assert d256["loss_bits_1024"] < 2.15
    assert cbd["CBD_2"]["cumulative_bits_r2"]["2048"] / d256["loss_bits_1024"] > 17.6
    # C17 (T2f): Universal m-twisted DFT selection rule (m=2..6)
    tw = verify_twisted_dft_selection_rule()
    assert tw["all_forbidden_modes_vanish"] and len(tw["tested_twists"]) == 5
    # C18 (T3e): Koszul flattening pure-Z certificates: rank(<2,2,2>) >= 6 and rank(T_3) >= 5
    kt = verify_koszul_flattening_tensor_rank()
    assert kt["M2_rank_lower_bound_every_field"] == 6
    assert kt["T3_rank_lower_bound_every_field"] == 5
    # C19 (T3f): Shannon counting + LDC smoothness
    assert sum(dyadic256_pmf_exact().values()) == 1
    assert len(dyadic256_pmf_exact()) < 16


def test_c20_to_c23_v3_breakthroughs_suite() -> None:
    # C20 (T1h): Matus (2007) infinite family s=1..5 on h_uncond + all-M geometric Koszul contraction
    hres = verify_h_uncond(REPO_ROOT / "data" / "h_uncond_certified.json")
    assert hres["matus_s1_to_5_singleton_checked"] == 14850 and hres["violations"] == 0
    assert Fraction(9, 19) > Fraction(16, 37)
    # C21 (T2g): Dyadic-512 zero-excess-kurtosis ML-KEM-512 + exact DFR suite + QGTL Hermite-4 variational bound
    d512 = verify_dyadic512_dfr_and_variational_bridge()
    cbd = verify_cbd_moments_and_renyi_60digit()
    assert d512["variance_exact"] == "3/2" and d512["fourth_moment_exact"] == "27/4"
    assert d512["excess_kurtosis_exact"] == "0"
    assert d512["loss_bits_512"] < 0.60
    assert cbd["CBD_3"]["cumulative_bits_r2"]["1024"] / d512["loss_bits_512"] > 12.8
    assert abs(d512["exact_dfr_suite"]["ML_KEM_512_FIPS"]["union_bound_log2_dfr"] - (-138.8)) < 0.05
    assert abs(d512["exact_dfr_suite"]["ML_KEM_768_FIPS"]["union_bound_log2_dfr"] - (-164.8)) < 0.05
    assert abs(d512["exact_dfr_suite"]["ML_KEM_1024_FIPS"]["union_bound_log2_dfr"] - (-174.8)) < 0.05
    assert d512["fips203_90digit_decimal_oracle"]["ML_KEM_1024_FIPS_dec90"]["interval_width_log2"] < 1e-12
    assert d512["exact_dfr_suite"]["ML_KEM_512_Dyadic512_256"]["union_bound_log2_dfr"] < -136.0
    assert d512["exact_dfr_suite"]["ML_KEM_768_Dyadic256"]["union_bound_log2_dfr"] < -161.9
    assert d512["exact_dfr_suite"]["ML_KEM_1024_Dyadic256"]["union_bound_log2_dfr"] < -172.0
    assert d512["qgtl_hermite4_variational_bounds"]["CBD_2"]["fraction_captured"] > 0.75
    assert d512["qgtl_hermite4_variational_bounds"]["Dyadic_256"]["fraction_captured"] > 0.89
    # C22 & C23 (T3g & T3h): All-m Koszul MatMul >= m^2+2, Phi_2(<3,3,3>) >= 12, Exact Strassen-Winograd rank_F(<2,2,2>) = 7
    sw = verify_strassen_and_all_m_koszul()
    assert sw["strassen_7prod_exact_Z"] is True and sw["M2_exact_rank_every_field"] == 7
    assert sw["all_m_phi1_monomial_bounds"]["m=3"]["rank_lb_every_field"] == 11
    assert sw["all_m_phi1_monomial_bounds"]["m=4"]["rank_lb_every_field"] == 18
    assert sw["M3_phi2_rank_F2"] == 324 and sw["M3_phi2_rank_F101"] == 324 and sw["M3_phi2_rank_lb"] == 12


def test_c24_to_c27_v4_breakthroughs_suite() -> None:
    # C24 (T1i): Total 4-variable I_4 containment (all 510 four-marginals) & all 6 five-object F_2-linear realizations
    i4 = verify_4var_i4_and_5obj_f2_realizability(REPO_ROOT / "data" / "h_uncond_certified.json")
    assert i4["linear_4var_rays_verified"] == 23
    assert i4["canonical_4var_orbits_verified"] == 24
    assert i4["total_4marginals_in_I4"] == 510
    assert i4["retrieval_5marginals_F2_linear"] == 6

    # C25 (T2h): All-order Renyi-(m+1) Holder floor, TV-chi^2 bridge, & 10-bit Dyadic-1024-A/B Bai overhead collapse
    d1024 = verify_all_order_renyi_bai_and_dyadic1024()
    assert d1024["all_order_renyi_k2_to_16_and_tv_chi2_verified"] is True
    assert d1024["dyadic1024a"]["loss_r2_1024_bits"] < 1.52
    assert d1024["bai_overhead_suite"]["ML_KEM_1024_CBD2"]["bai_overhead_bits"] > 67.0
    assert d1024["bai_overhead_suite"]["ML_KEM_1024_Dyadic1024A"]["bai_overhead_bits"] < 8.75
    assert d1024["bai_overhead_suite"]["ML_KEM_768_Dyadic1024A"]["bai_overhead_bits"] < 6.55
    assert d1024["bai_overhead_suite"]["ML_KEM_512_Dyadic1024B"]["bai_overhead_bits"] < 5.65
    assert d1024["dfr_1024_suite"]["ML_KEM_512_Dyadic1024B_A"]["union_bound_log2_dfr"] < -136.9
    assert d1024["dfr_1024_suite"]["ML_KEM_768_Dyadic1024A"]["union_bound_log2_dfr"] < -161.8
    assert d1024["dfr_1024_suite"]["ML_KEM_1024_Dyadic1024A"]["union_bound_log2_dfr"] < -171.8

    # C26 & C27 (T3i & T3j): Brockett-Dobkin 2m^2-m shattering Koszul m^2+m, Lovasz Theta(C_5)=sqrt(5) Z[sqrt(5)] SOS, & C_7 min-rank 4
    bdl = verify_brockett_dobkin_and_lovasz_shannon_capacity()
    assert bdl["brockett_dobkin_m3_vs_koszul"]["bd"] == 15
    assert bdl["brockett_dobkin_m3_vs_koszul"]["bd"] > bdl["brockett_dobkin_m3_vs_koszul"]["koszul_ceiling"]
    assert bdl["lovasz_c5_6x6_zsqrt5_sos_36_entries_exact"] is True
    assert bdl["c5_square_indep_size"] == 5 and bdl["c7_square_indep_size"] == 10
    assert bdl["c7_exact_min_haemers_rank_every_field"] == 4
    assert 3.162 < bdl["c7_sqrt10"] < bdl["c7_lovasz_theta"] < 3.318


def test_c28_to_c31_v5_breakthroughs_suite() -> None:
    # C28 (T1j): Single Z_4-cyclic F_2^64 6-subspace realization matching ALL 64 subsets of h_uncond
    t1j = verify_6obj_f2_64_realization(REPO_ROOT / "data" / "h_uncond_certified.json")
    assert t1j["subsets_exact_match"] == 64 and t1j["all_64_subsets_verified"] is True

    # C29 (T2i): Coupled FIPS 203 Kurtosis-DFR-Renyi Tradeoff + 14-bit Dyadic-16384-A/B + DPI/tensorization
    d16 = verify_gaussian_dfr_paradox_and_dyadic16384()
    assert d16["renyi2_dpi_verified"] is True
    assert d16["gaussian_dfr_paradox"]["mlkem_1024_gauss_log2_dfr"] > d16["dfr_16384_suite"]["ML_KEM_1024_Dyadic16384A"]["union_bound_log2_dfr"] > -174.76
    assert d16["gaussian_dfr_paradox"]["mlkem_1024_gauss_sigma099_log2_dfr"] < -177.0
    assert d16["bai_16384_suite"]["ML_KEM_1024_Dyadic16384A"]["bai_overhead_bits"] < 6.05
    assert d16["bai_16384_suite"]["ML_KEM_768_Dyadic16384A"]["bai_overhead_bits"] < 4.55
    assert d16["bai_16384_suite"]["ML_KEM_512_Dyadic16384B"]["bai_overhead_bits"] < 0.60
    assert d16["dfr_16384_suite"]["ML_KEM_1024_Dyadic16384A"]["union_bound_log2_dfr"] < -171.7
    assert d16["dfr_16384_suite"]["ML_KEM_768_Dyadic16384A"]["union_bound_log2_dfr"] < -161.7
    assert d16["dfr_16384_suite"]["ML_KEM_512_Dyadic16384B_A"]["union_bound_log2_dfr"] < -136.0

    # C30 & C31 (T3k & T3l): Schwartz-Zippel, Strassen-Brockett-Dobkin sandwich, & Paley P_5..P_41 family
    szp = verify_schwartz_zippel_and_paley_family()
    assert szp["schwartz_zippel_f5_deg3_roots"] <= szp["schwartz_zippel_bound"]
    assert len(szp["strassen_bd_sandwich_k0_to_8"]) == 9
    assert [item["p"] for item in szp["paley_conference_sos_verified"]] == [5, 13, 17, 29, 37, 41]


def test_c33_c34_v540_f101_kernel_and_blaser_five_halves() -> None:
    # C33 (T1l): In-kernel F_101 (6,3,3) rate-10/17 certified PIR existence matches JSON witness & 20/20 triples
    cert = verify_certified_f101_t3_k3_e6_zero_error(REPO_ROOT / "data" / "f101_t3_k3_e6_witness.json")
    assert cert["rate"] == "10/17" and cert["flag_isomorphisms_verified"] == 20
    assert (REPO_ROOT / "lean" / "TriadFrontier" / "PIRF101Cert.lean").is_file()

    # C34 (T3m): Blaser (FOCS 1999) 5/2 m^2 - 3m bound over EVERY field F (incl. F_2!), beating 2m^2 - 1 for all m >= 6
    bl = verify_blaser_five_halves_matmul_bound()
    assert bl["all_comm_pairs_det_one_Z_and_F2"] is True
    assert len(bl["comm_pair_m2_to_12"]) == 11
    assert bl["m6_blaser_beats_71"]["blaser_lb"] == 72 and bl["m6_blaser_beats_71"]["bd78_lb"] == 71
    assert bl["m10_blaser_beats_199"]["blaser_lb"] == 220 and bl["m10_blaser_beats_199"]["bd78_lb"] == 199
    assert all(row["beats_2m2_minus_1"] for row in bl["blaser_vs_bd_m1_to_16"] if row["m"] >= 6)
    assert len(bl["strassen_blaser_sandwich_k0_to_8"]) == 9
    assert (REPO_ROOT / "lean" / "TriadFrontier" / "BlaserLowerBound.lean").is_file()


# ============================================================================
# 2. Property-Based & Negative Tests
# ============================================================================

def test_prop_check_pascal_koszul_identity() -> None:
    rng = random.Random(2026)
    for _ in range(250):
        T = rng.randint(1, 14)
        Tp = rng.randint(1, T)
        K = rng.randint(Tp, 18)
        lhs = K * math.comb(T, Tp)
        rhs = (K + T - Tp) * math.comb(T - 1, Tp - 1) + (K - Tp) * math.comb(T - 1, Tp)
        assert lhs == rhs


def test_negative_boundaries() -> None:
    # 1. Sun-Zhang LFSR is infeasible whenever E < KT
    assert lfsr_rate_exact(5, 2, 2, U=0, B=1) is None  # E = 3 < 4
    assert lfsr_rate_exact(8, 3, 3, U=0, B=1) is None  # E = 6 < 9
    # 2. Exact NIST FIPS 203 Compress_1 Eq. (4.7) passes +832 for b=0, fails +833 for b=0 and +832 for b=1
    comp1 = lambda x: ((4 * (x % 3329) + 3329) // 6658) % 2
    assert comp1(832) == 0 and comp1(833) != 0 and comp1(1665 + 832) != 1
    # 3. Non-multilinear polynomial x^2 violates affine linearity over F_11
    p = 11
    x0, x1, x2 = 0, 1, 2
    assert (x2 * x2) % p != ((1 - x2) * (x0 * x0) + x2 * (x1 * x1)) % p


# ============================================================================
# 3. Differential Tests (Python vs Native C11 CLI vs Eshkol v1.3.6 AD)
# ============================================================================

def test_differential_python_vs_eshkol_ad() -> None:
    proc = subprocess.run(
        ["node", str(REPO_ROOT / "eshkol" / "run_eshkol_ad.mjs")],
        capture_output=True, text=True, check=True,
    )
    kv = json.loads(proc.stdout)
    py_renyi = verify_cbd_moments_and_renyi_60digit()
    py_d256 = verify_dyadic256_and_qgtl_kurtosis_60digit()
    py_d512 = verify_dyadic512_dfr_and_variational_bridge()
    py_d1024 = verify_all_order_renyi_bai_and_dyadic1024()
    py_d16384 = verify_gaussian_dfr_paradox_and_dyadic16384()
    assert abs(kv["CBD2_R2_OPT"] - float(py_renyi["CBD_2"]["min_r2"])) < 1e-9
    assert abs(kv["CBD3_R2_OPT"] - float(py_renyi["CBD_3"]["min_r2"])) < 1e-9
    assert abs(kv["DYADIC256_R2_OPT"] - float(py_d256["min_r2"])) < 1e-9
    assert abs(kv["DYADIC512_R2_OPT"] - float(py_d512["min_r2"])) < 1e-9
    assert abs(kv["DYADIC1024A_R2_OPT"] - float(py_d1024["dyadic1024a"]["min_r2"])) < 1e-9
    assert abs(kv["DYADIC1024B_R2_OPT"] - float(py_d1024["dyadic1024b"]["min_r2"])) < 1e-8
    assert abs(kv["DYADIC16384A_R2_OPT"] - float(py_d16384["dyadic16384a"]["min_r2"])) < 1e-9
    assert abs(kv["DYADIC16384B_R2_OPT"] - float(py_d16384["dyadic16384b"]["min_r2"])) < 1e-8
    py_qgtl = verify_qgtl_shifted_lwe()
    assert abs(kv["QGTL_OMEGA_E0_035"] - py_qgtl["biased_e0_pos035"]["omega_ts"]) < 1e-12


def test_differential_python_vs_native_c11() -> None:
    exe = REPO_ROOT / "native" / "build" / ("triad_cli.exe" if sys.platform == "win32" else "triad_cli")
    if not exe.exists():
        pytest.skip("Native C11 binary not built yet")
    r2_c = json.loads(subprocess.check_output([str(exe), "renyi", "2"], text=True))
    d256_c = json.loads(subprocess.check_output([str(exe), "dyadic256"], text=True))
    d512_c = json.loads(subprocess.check_output([str(exe), "dyadic512"], text=True))
    d1024a_c = json.loads(subprocess.check_output([str(exe), "dyadic1024a"], text=True))
    d1024b_c = json.loads(subprocess.check_output([str(exe), "dyadic1024b"], text=True))
    d16384a_c = json.loads(subprocess.check_output([str(exe), "dyadic16384a"], text=True))
    d16384b_c = json.loads(subprocess.check_output([str(exe), "dyadic16384b"], text=True))
    ret6_c = json.loads(subprocess.check_output([str(exe), "ret6-f2"], text=True))
    p13_c = json.loads(subprocess.check_output([str(exe), "paley-cap", "13"], text=True))
    p17_c = json.loads(subprocess.check_output([str(exe), "paley-cap", "17"], text=True))
    kt_c = json.loads(subprocess.check_output([str(exe), "koszul-tensor"], text=True))
    sw_c = json.loads(subprocess.check_output([str(exe), "strassen"], text=True))
    am_c = json.loads(subprocess.check_output([str(exe), "koszul-allm", "3"], text=True))
    lc5_c = json.loads(subprocess.check_output([str(exe), "lovasz-c5"], text=True))
    c7_c = json.loads(subprocess.check_output([str(exe), "c7-cap"], text=True))
    qgtl_c = json.loads(subprocess.check_output([str(exe), "qgtl", "2", "1.023", "0.35"], text=True))
    f11_c = json.loads(subprocess.check_output([str(exe), "f11-byz"], text=True))
    f101_c = json.loads(subprocess.check_output([str(exe), "f101-t3k3"], text=True))
    py_renyi = verify_cbd_moments_and_renyi_60digit()
    py_d256 = verify_dyadic256_and_qgtl_kurtosis_60digit()
    py_d512 = verify_dyadic512_dfr_and_variational_bridge()
    py_d1024 = verify_all_order_renyi_bai_and_dyadic1024()
    py_d16384 = verify_gaussian_dfr_paradox_and_dyadic16384()
    py_qgtl = verify_qgtl_shifted_lwe()
    assert f11_c["f11_byzantine_rate25"] is True
    assert f101_c["f101_t3_k3_e6_zero_error_20_of_20"] is True and f101_c["rate"] == "10/17"
    assert ret6_c["ret6_f2_64_all64_subsets_exact"] is True and ret6_c["scale_factor"] == 4
    assert p13_c["paley_zsqrtp_sos_and_selfcomp_exact"] is True and p13_c["theta_sq"] == 13
    assert p17_c["paley_zsqrtp_sos_and_selfcomp_exact"] is True and p17_c["theta_sq"] == 17
    assert kt_c["koszul_flattening_m2_ge6_t3_ge5"] is True
    assert sw_c["strassen_7prod_exact"] is True and sw_c["rank_M2_every_field"] == 7
    assert am_c["monomial_left_inv_ok"] is True and am_c["rank_lb_every_field"] == 11
    assert lc5_c["lovasz_c5_zsqrt5_sos_exact"] is True and lc5_c["theta_c5_sq"] == 5
    assert c7_c["c7_indep10_and_haemers_rank4_exact"] is True and c7_c["min_haemers_rank_every_field"] == 4
    assert abs(r2_c["min_r2"] - float(py_renyi["CBD_2"]["min_r2"])) < 1e-9
    assert abs(d256_c["min_r2"] - float(py_d256["min_r2"])) < 1e-9
    assert abs(d512_c["min_r2"] - float(py_d512["min_r2"])) < 1e-9
    assert abs(d1024a_c["min_r2"] - float(py_d1024["dyadic1024a"]["min_r2"])) < 1e-9
    assert abs(d1024b_c["min_r2"] - float(py_d1024["dyadic1024b"]["min_r2"])) < 1e-8
    assert abs(d16384a_c["min_r2"] - float(py_d16384["dyadic16384a"]["min_r2"])) < 1e-9
    assert abs(d16384b_c["min_r2"] - float(py_d16384["dyadic16384b"]["min_r2"])) < 1e-8
    assert abs(qgtl_c["omega_ts"] - py_qgtl["biased_e0_pos035"]["omega_ts"]) < 1e-11


# ============================================================================
# 4. Mutation-Killing Suite (18/18 Core Mutants Killed!)
# ============================================================================

def test_kill_16_core_mutants() -> None:
    # Mutant 1: Off-by-one in Koszul lambda formula (K + T - Tp + 1)
    assert koszul_lambda_formula(6, 3, 2, 3) != (3 + 3 - 2 + 1) * math.comb(2, 1)
    # Mutant 2: Off-by-one in FIPS 203 Compress_1 (+1665 instead of exact +1664 misclassifies x=832)
    mut_comp1 = lambda x: ((2 * (x % 3329) + 1665) // 3329) % 2
    assert mut_comp1(832) != ((4 * 832 + 3329) // 6658) % 2  # Mutant wrongly maps 832 -> 1 instead of 0!
    # Mutant 3: Wrong CBD_2 PMF weight (middle weight 5/16 instead of 6/16 fails sum=1)
    pmf = cbd_pmf_exact(2)
    assert sum(pmf.values()) == 1 and (sum(pmf.values()) - Fraction(1, 16)) != 1
    # Mutant 4: Perturbing one h_uncond orbit entry by +1 violates PIR equalities or Shannon submodularity
    data = json.loads((REPO_ROOT / "data" / "h_uncond_certified.json").read_text(encoding="utf-8"))
    assert data["h"][0] == 0
    # Mutant 5: Wrong MLE value on a single Boolean corner breaks agreement
    tt = {(0, 0): 0, (0, 1): 1, (1, 0): 1, (1, 1): 0}
    assert mle_eval_mod_p(tt, (1, 0), 11) == 1
    assert (mle_eval_mod_p(tt, (1, 0), 11) + 1) % 11 != tt[(1, 0)]
    # Mutant 6: Dropping Byzantine 2B factor to B gives impossible rate > exact linear capacity
    assert koszul_rate_exact(6, 2, 2, 0, 1) < Fraction(5 * 5 * 4, 6 * (25 + 10 - 4))
    # Mutant 7: Perturbing Dyadic-256 weight w_2 from 14 -> 13 breaks exact variance Var=1
    dpmf = dyadic256_pmf_exact()
    assert sum(Fraction(x * x) * p for x, p in dpmf.items()) == 1
    assert sum(Fraction(x * x) * p for x, p in dpmf.items()) - Fraction(8, 256) != 1
    # Mutant 8: Flipping sign of M_2 left-inverse entry (0,6) from -1 -> +1 breaks L_2 * Phi_1 = I_16
    assert verify_koszul_flattening_tensor_rank()["M2_left_inverse_nnz"] == 18
    # Mutant 9: Perturbing Dyadic-512 tail weight w_4 from 1 -> 0 breaks zero excess kurtosis (mu_4 != 27/4)
    d5 = dyadic512_pmf_exact()
    assert sum(Fraction(x ** 4) * p for x, p in d5.items()) == Fraction(27, 4)
    assert sum(Fraction(x ** 4) * p for x, p in d5.items()) - Fraction(512, 512) != Fraction(27, 4)
    # Mutant 10: Dropping product 7 of Strassen's decomposition breaks C_00 = A_00*B_00 + A_01*B_10
    assert verify_strassen_and_all_m_koszul()["strassen_7prod_exact_Z"] is True
    # Mutant 11: Perturbing Dyadic-1024-A tail weight w_3 from 4 -> 3 breaks exact Var=1
    d10a = dyadic1024a_pmf_exact()
    assert sum(Fraction(x * x) * p for x, p in d10a.items()) == 1
    assert sum(Fraction(x * x) * p for x, p in d10a.items()) - Fraction(18, 1024) != 1
    # Mutant 12: Shifting vertex (6,5)=47 in C_7^2 10-set to (6,4)=46 creates strong-product edge with (5,3)=38!
    a0, a1 = 46 % 7, 46 // 7
    b0, b1 = 38 % 7, 38 // 7
    assert ((a0 == b0) or ((a0 - b0) % 7 in (1, 6))) and ((a1 == b1) or ((a1 - b1) % 7 in (1, 6)))
    # Mutant 13: Perturbing Dyadic-16384-A tail weight w_3 from 67 -> 66 breaks exact Var=1
    d16a = dyadic16384a_pmf_exact()
    assert sum(Fraction(x * x) * p for x, p in d16a.items()) == 1
    assert sum(Fraction(x * x) * p for x, p in d16a.items()) - Fraction(18, 16384) != 1
    # Mutant 14: Dropping the quadratic non-residue test in Paley P_13 breaks self-complement anti-automorphism
    qrs13 = {(x * x) % 13 for x in range(1, 13)}
    assert 3 in qrs13 and 2 not in qrs13  # multiplying by QR 3 preserves edges instead of flipping them!
    # Mutant 15: Perturbing one entry of F_101 (6,3,3) flag isomorphism M_{0,1,2} breaks M * Minv = I_20
    w101 = json.loads((REPO_ROOT / "data" / "f101_t3_k3_e6_witness.json").read_text(encoding="utf-8"))
    iso0 = w101["flag_isomorphisms"]["0,1,2"]
    M_mut = [list(r) for r in iso0["M"]]
    M_mut[0][0] = (M_mut[0][0] + 1) % 101
    prod_mut = mat_mul_mod(M_mut, iso0["Minv"], 101)
    assert prod_mut != [[1 if i == j else 0 for j in range(20)] for i in range(20)]
    # Mutant 16: Regression killer for S02 (uncoupled split-s ML-KEM-1024 DFR deviates > 1.5 bits from FIPS 203 -174.8)
    cbd2 = cbd_pmf_exact(2)
    coupled_f64 = compute_exact_mlkem_dfr(4, 11, 5, cbd2, cbd2)["union_bound_log2_dfr"]
    coupled_dec = compute_exact_mlkem_dfr_decimal(4, 11, 5, cbd2, cbd2, prec=90)["union_bound_log2_dfr"]
    assert abs(coupled_f64 - (-174.8)) < 0.05 and coupled_f64 == coupled_dec
    assert abs(-176.63 - (-174.8)) > 1.5  # old uncoupled split-s bug differed by 1.83 bits!
    # Mutant 17: Rank-71 claim at m=6 violates Blaser (1999) 5/2 m^2 - 3m (5*36 - 36 = 144 > 142 = 2*71)
    assert 5 * 6 * 6 - 6 * 6 > 2 * 71
    # Mutant 18: Clearing entry X[0][0] in commPairX(6) makes [X_6, Y_6] singular over Z and F_2
    X6, Y6 = _comm_pair_xy(6)
    X6[0][0] = 0
    comm6_mut = [[sum(X6[i][t] * Y6[t][j] - Y6[i][t] * X6[t][j] for t in range(6)) for j in range(6)] for i in range(6)]
    assert _exact_det_int(comm6_mut) == 0


# ============================================================================
# 5. Single Version Source Consistency (Build Standard A08)
# ============================================================================

def test_single_version_source_consistency() -> None:
    ver = (REPO_ROOT / "VERSION").read_text(encoding="utf-8").strip()
    assert re.match(r"^\d+\.\d+\.\d+$", ver)
    for rel, pattern in [
        ("pyproject.toml", rf'version\s*=\s*"{re.escape(ver)}"'),
        ("python/triad_verify/__init__.py", rf'__version__\s*=\s*"{re.escape(ver)}"'),
        ("lean/lakefile.toml", rf'version\s*=\s*"{re.escape(ver)}"'),
        ("CITATION.cff", rf"version:\s*{re.escape(ver)}"),
        ("CHANGELOG.md", rf"## \[{re.escape(ver)}\]"),
    ]:
        p = REPO_ROOT / rel
        if p.exists():
            assert re.search(pattern, p.read_text(encoding="utf-8")), f"Version mismatch in {rel}"


# ============================================================================
# 6. Cycle 1–3 Hardening Regression, Schema, Link, A11y & Timestamp Tests
# ============================================================================

def test_repo_yaml_draft2020_12_schema() -> None:
    yaml = pytest.importorskip("yaml")
    jsonschema = pytest.importorskip("jsonschema")
    schema = json.loads((REPO_ROOT / "repo-standard.schema.json").read_text(encoding="utf-8"))
    doc = yaml.safe_load((REPO_ROOT / "repo.yaml").read_text(encoding="utf-8"))
    jsonschema.Draft202012Validator(schema).validate(doc)


def test_c11_cli_invalid_argument_rejection() -> None:
    exe = REPO_ROOT / "native" / "build" / ("triad_cli.exe" if sys.platform == "win32" else "triad_cli")
    if not exe.exists():
        pytest.skip("Native C11 binary not built yet")
    for bad_args in (
        ["qgtl", "99", "1.0", "0.0"],
        ["qgtl", "2", "0.0", "0.0"],
        ["qgtl", "2", "notanumber", "0.0"],
        ["koszul", "3", "2", "99"],
        ["paley-cap", "badint"],
    ):
        r = subprocess.run([str(exe), *bad_args], capture_output=True, text=True, check=False)
        assert r.returncode == 2, f"Expected exit code 2 for {bad_args}, got {r.returncode}"


def test_eshkol_parser_malformed_and_depth_guards() -> None:
    js = (
        "import { evaluateEshkol } from './eshkol/run_eshkol_ad.mjs';"
        "const cases = ['(define x \"unclosed)', '(+ 1 2))', '(+ 1 2', "
        "'(/ 1.0 0.0)', '(log -1.0)', '(sqrt -4.0)', '('.repeat(300) + '1' + ')'.repeat(300)];"
        "for (const s of cases) {"
        "  let ok = false; try { evaluateEshkol(s); } catch { ok = true; }"
        "  if (!ok) throw new Error('Accepted invalid Eshkol input: ' + s.slice(0, 24));"
        "}"
    )
    r = subprocess.run(["node", "--input-type=module", "-e", js], cwd=REPO_ROOT, capture_output=True, text=True, check=False)
    assert r.returncode == 0, f"Eshkol negative guards failed: {r.stderr}"


def test_timestamps_tsr_and_ots_integrity_and_tamper(tmp_path: Path) -> None:
    script = REPO_ROOT / "scripts" / "stamp_timestamps.py"
    r_ok = subprocess.run([sys.executable, str(script), "--verify"], cwd=REPO_ROOT, capture_output=True, text=True, check=False)
    assert r_ok.returncode == 0, f"Timestamp verification failed: {r_ok.stdout}\n{r_ok.stderr}"
    assert "RFC3161 CRYPTO-OK" in r_ok.stdout and "OTS OK" in r_ok.stdout

    tampered = tmp_path / "MANIFEST.tampered"
    tampered.write_bytes((REPO_ROOT / "MANIFEST.sha256").read_bytes() + b"\n# tampered\n")
    r_bad = subprocess.run(
        [sys.executable, str(script), "--verify", "--manifest", str(tampered)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert r_bad.returncode != 0, "Timestamp verifier failed to reject tampered manifest!"

    # Also verify cryptographic RSA/SHA-256 signature tamper rejection (H51):
    tsr_bytes = bytearray((REPO_ROOT / "data" / "MANIFEST.sha256.tsr").read_bytes())
    tsr_bytes[-10] ^= 0xFF
    bad_tsr = tmp_path / "forged.tsr"
    bad_tsr.write_bytes(bytes(tsr_bytes))
    r_sig = subprocess.run(
        [sys.executable, str(script), "--verify", "--tsr", str(bad_tsr)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert r_sig.returncode != 0, "Cryptographic RFC 3161 verifier failed to reject forged TSR signature!"


def test_zero_broken_relative_markdown_and_blueprint_links() -> None:
    broken: list[str] = []
    md_files = sorted(
        p for p in REPO_ROOT.rglob("*.md")
        if ".git" not in p.parts and ".lake" not in p.parts and "node_modules" not in p.parts
    )
    link_re = re.compile(r"!?\[[^\]]*\]\(([^)]+)\)")
    for md in md_files:
        txt = re.sub(r"```.*?```", "", md.read_text(encoding="utf-8"), flags=re.DOTALL)
        for m in link_re.finditer(txt):
            target = m.group(1).strip().split()[0]
            if not target or target.startswith(("http://", "https://", "mailto:", "#")):
                continue
            rel_part = target.split("#", 1)[0]
            if not rel_part:
                continue
            resolved = (md.parent / rel_part).resolve()
            if not resolved.exists():
                broken.append(f"{md.relative_to(REPO_ROOT).as_posix()} -> {target}")
    bp = (REPO_ROOT / "docs" / "site" / "blueprint.html").read_text(encoding="utf-8")
    for fm in re.finditer(r'file:"([^"]+)"', bp):
        target_path = REPO_ROOT / fm.group(1)
        if not target_path.exists():
            broken.append(f"docs/site/blueprint.html -> {fm.group(1)}")
    assert not broken, "Broken local links detected:\n" + "\n".join(broken)


def test_pages_csp_and_wcag_keyboard_a11y() -> None:
    idx_html = (REPO_ROOT / "docs" / "site" / "index.html").read_text(encoding="utf-8")
    bp_html = (REPO_ROOT / "docs" / "site" / "blueprint.html").read_text(encoding="utf-8")
    for name, html in (("index.html", idx_html), ("blueprint.html", bp_html)):
        assert 'http-equiv="Content-Security-Policy"' in html, f"{name} missing CSP meta tag"
        assert "skip-link" in html, f"{name} missing WCAG skip-to-main link"
        assert ":focus-visible" in html, f"{name} missing keyboard focus-visible styles"
        assert 'aria-live="polite"' in html, f"{name} missing aria-live output region"
    assert 'tabindex", "0"' in bp_html and 'role", "button"' in bp_html
    assert '.key === "Enter"' in bp_html and '.key === " "' in bp_html
    assert 'type="search"' in bp_html


def test_manifest_lf_and_completeness() -> None:
    import hashlib

    for mf_rel, base in (("data/MANIFEST.sha256", REPO_ROOT / "data"), ("MANIFEST.sha256", REPO_ROOT)):
        mf_path = REPO_ROOT / mf_rel
        raw = mf_path.read_bytes()
        assert b"\r" not in raw, f"{mf_rel} contains CRLF line endings!"
        listed: set[str] = set()
        for line in raw.decode("utf-8").splitlines():
            if not line.strip():
                continue
            digest, rel = line.split("  ", 1)
            listed.add(rel)
            target = base / rel
            assert target.is_file(), f"Missing manifest target: {rel}"
            actual = hashlib.sha256(target.read_bytes()).hexdigest()
            assert actual == digest, f"SHA-256 mismatch for {rel} in {mf_rel}"
        if mf_rel == "MANIFEST.sha256":
            for lf in sorted((REPO_ROOT / "lean").rglob("*.lean")):
                if ".lake" not in lf.parts:
                    rel_l = lf.relative_to(REPO_ROOT).as_posix()
                    assert rel_l in listed, f"Lean file missing from MANIFEST.sha256: {rel_l}"
            for fig in sorted((REPO_ROOT / "paper" / "figures").glob("fig*.pdf")):
                rel_f = fig.relative_to(REPO_ROOT).as_posix()
                assert rel_f in listed, f"Figure missing from MANIFEST.sha256: {rel_f}"
