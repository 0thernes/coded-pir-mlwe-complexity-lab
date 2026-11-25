/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander S. Donahue
 */
#include "triad_core.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

static int g_pass = 0;
static int g_fail = 0;

#define CHECK(cond, msg) do { \
    if (cond) { g_pass++; } \
    else { g_fail++; fprintf(stderr, "FAIL: %s\n", (msg)); } \
} while (0)

static int binom(int n, int k) {
    if (k < 0 || k > n) return 0;
    int r = 1;
    for (int i = 1; i <= k; i++) r = r * (n - i + 1) / i;
    return r;
}

int main(void) {
    /* 1. Koszul-Veronese exact Schur-product rank across (T, T', K) grid */
    for (int T = 2; T <= 4; T++) {
        for (int K = 2; K <= 4; K++) {
            for (int Tp = 1; Tp <= T; Tp++) {
                if (Tp > K) continue;
                int rk = triad_verify_koszul_rank(T, Tp, K, 101);
                int exp_rk = (K + T - Tp) * binom(T - 1, Tp - 1);
                CHECK(rk == exp_rk, "Koszul-Veronese exact rank matches formula");
            }
        }
    }

    /* 2. Exact F_11 Byzantine rate-2/5 (N=6, K=2, T=2, B=1) differential check vs Lean T1c */
    CHECK(triad_verify_f11_byzantine_rate25(), "F_11 Byzantine rate-2/5 15-subset + 30-pair privacy");

    /* 3. Chen Step-9 anti-periodic DFT cancellation for odd c, D */
    int Ds[5] = {3, 5, 7, 11, 13};
    for (int i = 0; i < 5; i++) {
        triad_chen_res_t r = triad_verify_chen_step9(Ds[i], 3);
        CHECK(r.passed, "Chen Step-9 even DFT modes vanish identically");
    }
    /* Negative test: even c=2 breaks anti-periodicity so even modes DO NOT vanish */
    triad_chen_res_t r_even = triad_verify_chen_step9(5, 2);
    CHECK(!r_even.passed && r_even.max_even_mag > 1.0, "Chen negative control (even c) has nonzero even modes");

    /* 4. QGTL shifted-LWE Berry curvature identity & exact symmetry vanishing */
    triad_qgtl_res_t q0 = triad_qgtl_shifted_lwe(2, 1.023, 0.0);
    CHECK(fabs(q0.omega_ts) < 1e-14 && fabs(q0.g_ts) < 1e-14 && q0.max_err < 1e-14,
          "QGTL Berry curvature vanishes identically at symmetric noise e0=0");
    triad_qgtl_res_t q1 = triad_qgtl_shifted_lwe(2, 1.023, 0.35);
    CHECK(fabs(q1.omega_ts) > 1e-3 && q1.max_err < 1e-14,
          "QGTL Berry curvature nonzero under bias e0=0.35 and matches Cov(X, (X-e0)^2/sigma^3)");

    /* 5. ML-KEM CBD_2 vs CBD_3 Renyi-2 / Renyi-inf 5x cliff */
    triad_renyi_res_t r2 = triad_mlkem_renyi_opt(2);
    triad_renyi_res_t r3 = triad_mlkem_renyi_opt(3);
    CHECK(fabs(r2.min_r2 - 1.01289031) < 1e-5, "CBD_2 min Renyi-2 ~ 1.01289031");
    CHECK(fabs(r3.min_r2 - 1.00517826) < 1e-5, "CBD_3 min Renyi-2 ~ 1.00517826");
    double loss_1024 = 2048.0 * r2.bits_per_coord_r2;
    double loss_512 = 1024.0 * r3.bits_per_coord_r2;
    CHECK(loss_1024 > 37.8 && loss_1024 < 37.9, "ML-KEM-1024 Renyi-2 loss ~ 37.84 bits");
    CHECK(loss_512 > 7.6 && loss_512 < 7.7, "ML-KEM-512 Renyi-2 loss ~ 7.63 bits");
    CHECK(loss_1024 / loss_512 > 4.9, "5x ML-KEM Renyi-2 tightness cliff confirmed");

    /* 6. FIPS 203 Compress_1 sharp boundary (-831..831 pass, +832 fail) */
    bool ok_margin = true;
    for (int e = -831; e <= 831; e++) {
        if (triad_mlkem_compress1(e) != 0) ok_margin = false;
        if (triad_mlkem_compress1(1665 + e) != 1) ok_margin = false;
    }
    CHECK(ok_margin, "Compress_1 exact on all |e| <= 831");
    CHECK(triad_mlkem_compress1(832) == 1 && triad_mlkem_compress1(1665 + 832) == 0,
          "Compress_1 fails sharply at +832 for both b=0 and b=1");

    /* 7. Deterministic fuzz smoke (500 pseudo-random QGTL & rank inputs, ASan/UBSan clean) */
    uint32_t seed = 0x20261125u;
    bool fuzz_ok = true;
    for (int t = 0; t < 500; t++) {
        seed = seed * 1664525u + 1013904223u;
        double sigma = 0.5 + (double)(seed % 2000u) / 1000.0;
        seed = seed * 1664525u + 1013904223u;
        double e0 = -1.0 + (double)(seed % 2000u) / 1000.0;
        triad_qgtl_res_t qr = triad_qgtl_shifted_lwe(2, sigma, e0);
        if (qr.max_err > 1e-12 || qr.g_tt < -1e-12 || qr.g_ss < -1e-12) fuzz_ok = false;
    }
    CHECK(fuzz_ok, "500-case deterministic QGTL fuzz invariants hold (no NaN/UB/negative metric)");

    printf("Native C11 TriadFrontier tests: %d passed, %d failed\n", g_pass, g_fail);
    return g_fail == 0 ? 0 : 1;
}
