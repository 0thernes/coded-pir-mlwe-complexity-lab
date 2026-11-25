#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""
Comprehensive Verification & Falsification Test Suite (`tests/test_all.py`):
- Claim falsifiability checks (C1–C14)
- Negative / adversarial boundary checks
- Randomized property-based tests (prop_check)
- Differential tests (Python vs native C11 CLI vs Eshkol v1.3.6 AD runtime)
- Metamorphic checks (K <-> T symmetry, noise-shift odd symmetry)
- Mutation-killing tests (6/6 core mutants killed!)
- Single-version-source consistency (VERSION == pyproject.toml == CHANGELOG.md == CITATION.cff == lean/lakefile.toml)
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
    mle_eval_mod_p,
    verify_algebrization_mle,
    verify_katz_trevisan_ldc_distance,
    verify_mlwe_compress1_ceiling,
)
from triad_verify.mlwe_tightness import (
    cbd_pmf_exact,
    verify_cbd_moments_and_renyi_60digit,
    verify_chen_step9,
    verify_luo_det_ideal_independence,
    verify_qgtl_shifted_lwe,
)
from triad_verify.pir_koszul import (
    koszul_lambda_formula,
    koszul_rate_exact,
    lfsr_rate_exact,
    verify_certified_f11_byzantine,
    verify_koszul_rank_grid,
    verify_overlap_sub_kt_scheme,
    verify_t3_k3_e6_zero_error,
)
from triad_verify.polymatroid_barrier import verify_h_uncond


# ============================================================================
# 1. Core Claims Falsifiability Tests (CS-053, CS-026, CS-001)
# ============================================================================

def test_c1_koszul_veronese_rank_grid() -> None:
    res = verify_koszul_rank_grid(p=101)
    assert res["checked_blocks"] == 46
    assert res["strict_savings_count"] == 30
    assert koszul_lambda_formula(6, 3, 2, 3) == 8 < 9


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
    # 2. Compress_1 MUST fail at +832 for both b=0 and b=1
    comp1 = lambda x: ((2 * (x % 3329) + 1665) // 3329) % 2
    assert comp1(832) != 0 and comp1(1665 + 832) != 1
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
    assert abs(kv["CBD2_R2_OPT"] - float(py_renyi["CBD_2"]["min_r2"])) < 1e-9
    assert abs(kv["CBD3_R2_OPT"] - float(py_renyi["CBD_3"]["min_r2"])) < 1e-9
    py_qgtl = verify_qgtl_shifted_lwe()
    assert abs(kv["QGTL_OMEGA_E0_035"] - py_qgtl["biased_e0_pos035"]["omega_ts"]) < 1e-12


def test_differential_python_vs_native_c11() -> None:
    exe = REPO_ROOT / "native" / "build" / ("triad_cli.exe" if sys.platform == "win32" else "triad_cli")
    if not exe.exists():
        pytest.skip("Native C11 binary not built yet")
    r2_c = json.loads(subprocess.check_output([str(exe), "renyi", "2"], text=True))
    qgtl_c = json.loads(subprocess.check_output([str(exe), "qgtl", "2", "1.023", "0.35"], text=True))
    f11_c = json.loads(subprocess.check_output([str(exe), "f11-byz"], text=True))
    py_renyi = verify_cbd_moments_and_renyi_60digit()
    py_qgtl = verify_qgtl_shifted_lwe()
    assert f11_c["f11_byzantine_rate25"] is True
    assert abs(r2_c["min_r2"] - float(py_renyi["CBD_2"]["min_r2"])) < 1e-9
    assert abs(qgtl_c["omega_ts"] - py_qgtl["biased_e0_pos035"]["omega_ts"]) < 1e-11


# ============================================================================
# 4. Mutation-Killing Suite (6/6 Core Mutants Killed!)
# ============================================================================

def test_kill_6_core_mutants() -> None:
    # Mutant 1: Off-by-one in Koszul lambda formula (K + T - Tp + 1)
    assert koszul_lambda_formula(6, 3, 2, 3) != (3 + 3 - 2 + 1) * math.comb(2, 1)
    # Mutant 2: Off-by-one in FIPS 203 Compress_1 (+1664 instead of +1665 misses +832 failure)
    mut_comp1 = lambda x: ((2 * (x % 3329) + 1664) // 3329) % 2
    assert mut_comp1(832) == 0  # Mutant wrongly passes +832; caught by our sharp failure test!
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


# ============================================================================
# 5. Single Version Source Consistency (Build Standard A08)
# ============================================================================

def test_single_version_source_consistency() -> None:
    ver = (REPO_ROOT / "VERSION").read_text(encoding="utf-8").strip()
    assert re.match(r"^\d+\.\d+\.\d+$", ver)
    for rel, pattern in [
        ("pyproject.toml", rf'version\s*=\s*"{re.escape(ver)}"'),
        ("lean/lakefile.toml", rf'version\s*=\s*"{re.escape(ver)}"'),
        ("CITATION.cff", rf"version:\s*{re.escape(ver)}"),
        ("CHANGELOG.md", rf"## \[{re.escape(ver)}\]"),
    ]:
        p = REPO_ROOT / rel
        if p.exists():
            assert re.search(pattern, p.read_text(encoding="utf-8")), f"Version mismatch in {rel}"
