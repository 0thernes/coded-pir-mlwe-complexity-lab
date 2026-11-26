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

    /* 7. Deterministic fuzz smoke (500 pseudo-random QGTL & PSD invariants, ASan/UBSan clean) */
    uint32_t seed = 0x20261125u;
    bool fuzz_ok = true;
    for (int t = 0; t < 500; t++) {
        seed = seed * 1664525u + 1013904223u;
        double sigma = 0.5 + (double)(seed % 2000u) / 1000.0;
        seed = seed * 1664525u + 1013904223u;
        double e0 = -1.0 + (double)(seed % 2000u) / 1000.0;
        triad_qgtl_res_t qr = triad_qgtl_shifted_lwe(2, sigma, e0);
        double qgt_psd = 4.0 * qr.g_tt * qr.g_ss - qr.omega_ts * qr.omega_ts;
        if (qr.max_err > 1e-12 || qr.g_tt < -1e-12 || qr.g_ss < -1e-12 || qgt_psd < -1e-11) fuzz_ok = false;
    }
    CHECK(fuzz_ok, "500-case deterministic QGTL & Provost-Vallee PSD fuzz invariants hold");

    /* 8. v2.0.0 Optimal 8-Bit Dyadic-256 ML-KEM Noise (exact Var=1, 17.7x Renyi-2 reduction, CT sampler) */
    int hist[7] = {0};
    for (int b = 0; b < 256; b++) {
        int v = triad_dyadic256_sample_ct((uint8_t)b);
        if (v >= -3 && v <= 3) hist[v + 3]++;
    }
    CHECK(hist[0] == 1 && hist[1] == 14 && hist[2] == 63 && hist[3] == 100 &&
          hist[4] == 63 && hist[5] == 14 && hist[6] == 1,
          "Constant-time Dyadic-256 1-byte sampler matches exact weights (1,14,63,100,63,14,1)");
    triad_renyi_res_t rd = triad_mlkem_dyadic256_opt();
    double loss_d1024 = 2048.0 * rd.bits_per_coord_r2;
    CHECK(fabs(rd.min_r2 - 1.000723969787) < 1e-9, "Dyadic-256 min Renyi-2 matches 60-digit oracle");
    CHECK(loss_d1024 > 2.13 && loss_d1024 < 2.15 && (loss_1024 / loss_d1024) > 17.6,
          "Dyadic-256 compresses ML-KEM-1024 Renyi-2 loss by >17.6x (37.84 -> 2.14 bits)");

    /* 9. v2.0.0 Universal m-Twisted DFT selection rule (T2f: m=2,3,4,5,6) */
    for (int m = 2; m <= 6; m++) {
        double mf = 0.0;
        CHECK(triad_verify_twisted_dft(m, 5, 1, &mf), "Universal m-twisted DFT selection rule vanishes");
    }

    /* 10. v2.0.0 Universal Koszul Flattening pure-Z certificates (T3e: rank(<2,2,2>)>=6, rank(T_3)>=5) */
    CHECK(triad_verify_koszul_flattening_certs(), "Koszul flattening Z-inverses for M_2 and T_3 verified");

    /* 11. v3.0.0 Optimal 9-Bit Zero-Excess-Kurtosis Dyadic-512 for ML-KEM-512 (T2g) */
    int h512[9] = {0};
    for (int raw = 0; raw < 512; raw++) {
        int v = triad_dyadic512_sample_ct((uint16_t)raw);
        if (v >= -4 && v <= 4) h512[v + 4]++;
    }
    CHECK(h512[0] == 1 && h512[1] == 8 && h512[2] == 44 && h512[3] == 120 && h512[4] == 166 &&
          h512[5] == 120 && h512[6] == 44 && h512[7] == 8 && h512[8] == 1,
          "Constant-time Dyadic-512 9-bit sampler matches exact weights (1,8,44,120,166,120,44,8,1)");
    int sum_x2 = 0, sum_x4 = 0;
    for (int i = 0; i < 9; i++) {
        int x = i - 4;
        sum_x2 += h512[i] * x * x;
        sum_x4 += h512[i] * x * x * x * x;
    }
    CHECK(sum_x2 == 768 && sum_x4 == 3456,
          "Dyadic-512 exact Var=3/2 (768/512) and exact zero excess kurtosis mu_4=27/4 (3456/512)");
    triad_renyi_res_t rd512 = triad_mlkem_dyadic512_opt();
    double loss_d512 = 1024.0 * rd512.bits_per_coord_r2;
    CHECK(fabs(rd512.min_r2 - 1.000400858061) < 1e-9, "Dyadic-512 min Renyi-2 matches 60-digit oracle");
    CHECK(loss_d512 > 0.59 && loss_d512 < 0.60 && (loss_512 / loss_d512) > 12.8,
          "Dyadic-512 compresses ML-KEM-512 Renyi-2 loss by >12.8x (7.63 -> 0.59 bits)");

    /* 12. v3.0.0 Exact Strassen 7-product & All-m Koszul Monomial Left-Inverses (T3g/T3h) */
    CHECK(triad_verify_strassen_7prod(), "Strassen 7-product bilinear decomposition matches <2,2,2> over Z");
    for (int m = 2; m <= 4; m++) {
        CHECK(triad_verify_all_m_koszul_monomial(m), "All-m monomial left-inverse certifies rank(<m,m,m>) >= m^2+2");
    }

    printf("Native C11 TriadFrontier tests: %d passed, %d failed\n", g_pass, g_fail);
    return g_fail == 0 ? 0 : 1;
}
