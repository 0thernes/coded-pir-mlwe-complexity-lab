/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander S. Donahue
 *
 * TriadFrontier Native C11 Verification Core (`CS-053`, `CS-026`, `CS-001`)
 * Clean-room C11 implementations inspired by Tsotchke's Moonlab and QGTL architectures.
 */
#ifndef TRIAD_CORE_H
#define TRIAD_CORE_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

typedef struct {
    int64_t num;
    int64_t den;
} triad_rat_t;

typedef struct {
    double g_tt;
    double g_ss;
    double g_ts;
    double omega_ts;
    double cov_formula;
    double max_err;
} triad_qgtl_res_t;

typedef struct {
    int D;
    int c;
    double max_even_mag;
    double max_odd_mag;
    bool passed;
} triad_chen_res_t;

typedef struct {
    int eta;
    double sigma_opt_r2;
    double min_r2;
    double sigma_opt_rinf;
    double min_rinf;
    double bits_per_coord_r2;
} triad_renyi_res_t;

/* Exact modular arithmetic & finite-field rank over F_p (prime p < 65536). */
int triad_mod_inv(int a, int p);
int triad_rank_mod_p(const int *mat, int rows, int cols, int p);

/* CS-053: Exact Koszul-Veronese Schur-product rank verification & Byzantine F_11 audit. */
int triad_verify_koszul_rank(int T, int Tp, int K, int p);
bool triad_verify_f11_byzantine_rate25(void);

/* CS-026: Yilei Chen (2024/555) Step-9 anti-periodic DFT cancellation verifier. */
triad_chen_res_t triad_verify_chen_step9(int D, int c);

/* CS-026: QGTL shifted-LWE Fourier state metric & Berry curvature calculator. */
triad_qgtl_res_t triad_qgtl_shifted_lwe(int eta, double sigma, double e0);

/* CS-026: FIPS 203 CBD_eta & Optimal 8-Bit Dyadic-256 Renyi-2 optimizer, sampler & Compress_1. */
triad_renyi_res_t triad_mlkem_renyi_opt(int eta);
triad_renyi_res_t triad_mlkem_dyadic256_opt(void);
int triad_dyadic256_sample_ct(uint8_t byte);
int triad_mlkem_compress1(int x);

/* CS-026 <-> QC-042: Universal m-twisted DFT selection rule verifier (T2f). */
bool triad_verify_twisted_dft(int m, int D, int r, double *out_max_forb);

/* CS-053 <-> CS-004/CS-012: Pure-integer Koszul flattening left-inverse verifier (T3e). */
bool triad_verify_koszul_flattening_certs(void);

#endif /* TRIAD_CORE_H */
