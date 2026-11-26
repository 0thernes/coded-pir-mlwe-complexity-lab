/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander S. Donahue
 */
#include "triad_core.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

#ifndef M_PI
#define M_PI 3.14159265358979323846264338327950288
#endif

static int mod_norm(int a, int p) {
    int r = a % p;
    return r < 0 ? r + p : r;
}

static int mod_pow(int base, int exp, int p) {
    long long res = 1;
    long long b = mod_norm(base, p);
    int e = exp;
    while (e > 0) {
        if (e & 1) res = (res * b) % p;
        b = (b * b) % p;
        e >>= 1;
    }
    return (int)res;
}

int triad_mod_inv(int a, int p) {
    return mod_pow(a, p - 2, p);
}

int triad_rank_mod_p(const int *mat, int rows, int cols, int p) {
    if (rows <= 0 || cols <= 0 || p <= 1) return 0;
    int *A = (int *)malloc((size_t)rows * (size_t)cols * sizeof(int));
    if (!A) return -1;
    for (int i = 0; i < rows * cols; i++) {
        A[i] = mod_norm(mat[i], p);
    }
    int r = 0;
    for (int c = 0; c < cols && r < rows; c++) {
        int piv = -1;
        for (int i = r; i < rows; i++) {
            if (A[i * cols + c] != 0) {
                piv = i;
                break;
            }
        }
        if (piv < 0) continue;
        if (piv != r) {
            for (int j = c; j < cols; j++) {
                int tmp = A[r * cols + j];
                A[r * cols + j] = A[piv * cols + j];
                A[piv * cols + j] = tmp;
            }
        }
        int inv = triad_mod_inv(A[r * cols + c], p);
        for (int j = c; j < cols; j++) {
            A[r * cols + j] = (int)(((long long)A[r * cols + j] * inv) % p);
        }
        for (int i = 0; i < rows; i++) {
            if (i != r && A[i * cols + c] != 0) {
                int f = A[i * cols + c];
                for (int j = c; j < cols; j++) {
                    long long v = A[i * cols + j] - (long long)f * A[r * cols + j];
                    A[i * cols + j] = mod_norm((int)(v % p), p);
                }
            }
        }
        r++;
    }
    free(A);
    return r;
}

static int binom_small(int n, int k) {
    if (k < 0 || k > n) return 0;
    if (k == 0 || k == n) return 1;
    int res = 1;
    for (int i = 1; i <= k; i++) {
        res = res * (n - i + 1) / i;
    }
    return res;
}

/* Compute exact rank of Koszul-Veronese block (T, T', K) evaluated on (K+T-T') servers mod p. */
int triad_verify_koszul_rank(int T, int Tp, int K, int p) {
    if (T < 1 || Tp < 1 || Tp > T || K < 1 || T > 6) return -1;
    int dim_ext = binom_small(T, Tp);
    int rows_per_srv = binom_small(T - 1, Tp - 1);
    int n_srv = K + T - Tp;
    int total_rows = n_srv * rows_per_srv;
    int total_cols = K * dim_ext;

    /* Enumerate all Tp-subsets of {0..T-1} */
    int basis_Tp[64][6];
    int b_cnt = 0;
    for (int mask = 0; mask < (1 << T); mask++) {
        int pop = 0;
        for (int b = 0; b < T; b++) if (mask & (1 << b)) pop++;
        if (pop == Tp) {
            int idx = 0;
            for (int b = 0; b < T; b++) if (mask & (1 << b)) basis_Tp[b_cnt][idx++] = b;
            b_cnt++;
        }
    }

    int *M = (int *)calloc((size_t)total_rows * (size_t)total_cols, sizeof(int));
    if (!M) return -1;
    int row_cur = 0;

    for (int s = 0; s < n_srv; s++) {
        int a = s + 1;
        int u[6], g[8];
        for (int d = 0; d < T; d++) u[d] = mod_pow(a, d, p);
        for (int k = 0; k < K; k++) g[k] = mod_pow(a, k, p);

        /* Enumerate all (Tp-1)-subsets S of {1..T-1} */
        for (int smask = 0; smask < (1 << (T - 1)); smask++) {
            int pop = 0;
            for (int b = 0; b < T - 1; b++) if (smask & (1 << b)) pop++;
            if (pop != Tp - 1) continue;

            int S_elts[6];
            int s_idx = 0;
            for (int b = 0; b < T - 1; b++) if (smask & (1 << b)) S_elts[s_idx++] = b + 1;

            int w[64];
            memset(w, 0, sizeof(w));
            for (int d = 0; d < T; d++) {
                bool in_S = false;
                for (int q = 0; q < Tp - 1; q++) if (S_elts[q] == d) in_S = true;
                if (in_S) continue;

                int tup[6];
                int inv_cnt = 0;
                int tpos = 0;
                for (int q = 0; q < Tp - 1; q++) {
                    if (d > S_elts[q]) inv_cnt++;
                    tup[tpos++] = S_elts[q];
                }
                tup[tpos++] = d;
                /* insertion sort tup */
                for (int i = 1; i < Tp; i++) {
                    int key = tup[i];
                    int j = i - 1;
                    while (j >= 0 && tup[j] > key) { tup[j + 1] = tup[j]; j--; }
                    tup[j + 1] = key;
                }
                int bmatch = -1;
                for (int bi = 0; bi < b_cnt; bi++) {
                    bool eq = true;
                    for (int q = 0; q < Tp; q++) if (basis_Tp[bi][q] != tup[q]) { eq = false; break; }
                    if (eq) { bmatch = bi; break; }
                }
                if (bmatch >= 0) {
                    int sgn = (inv_cnt % 2) ? -1 : 1;
                    w[bmatch] = mod_norm(sgn * u[d], p);
                }
            }
            for (int k = 0; k < K; k++) {
                for (int bi = 0; bi < dim_ext; bi++) {
                    M[row_cur * total_cols + k * dim_ext + bi] = (int)(((long long)w[bi] * g[k]) % p);
                }
            }
            row_cur++;
        }
    }
    int rk = triad_rank_mod_p(M, total_rows, total_cols, p);
    free(M);
    return rk;
}

/* Certified F_11 Byzantine rate-2/5 (N=6, K=2, T=2, B=1, E=4) verifier matching Lean T1c. */
bool triad_verify_f11_byzantine_rate25(void) {
    const int p = 11;
    const int alphas[6] = {1, 2, 3, 4, 5, 6};
    const int A_sels[6][2][3] = {
        {{4, 10, 10}, {3, 2, 10}},
        {{3, 1, 1}, {2, 8, 10}},
        {{6, 9, 9}, {3, 0, 6}},
        {{3, 10, 6}, {5, 8, 7}},
        {{7, 3, 1}, {1, 1, 10}},
        {{10, 2, 5}, {4, 9, 6}}
    };
    const int B_sels[6][2][3] = {
        {{10, 8, 7}, {4, 0, 2}},
        {{2, 7, 1}, {10, 9, 7}},
        {{7, 0, 2}, {3, 2, 3}},
        {{3, 10, 0}, {10, 7, 7}},
        {{6, 10, 4}, {5, 0, 6}},
        {{5, 10, 1}, {2, 1, 0}}
    };
    /* Note: load exact V_mats and U_mats over F_11 */
    int V[6][3][6];
    int U[6][3][6];
    const int b2[6][2] = {{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}};
    memset(V, 0, sizeof(V));
    memset(U, 0, sizeof(U));
    for (int n = 0; n < 6; n++) {
        int a = alphas[n];
        int u[4] = {1, a % p, (a * a) % p, (a * a * a) % p};
        for (int ki = 0; ki < 3; ki++) {
            int k = ki + 1;
            for (int r = 0; r < 4; r++) {
                if (r == k) continue;
                int lo = r < k ? r : k;
                int hi = r < k ? k : r;
                int sgn = r < k ? 1 : -1;
                for (int bi = 0; bi < 6; bi++) {
                    if (b2[bi][0] == lo && b2[bi][1] == hi) {
                        V[n][ki][bi] = mod_norm(sgn * u[r], p);
                    }
                }
            }
        }
        U[n][0][0] = 1;
        U[n][1][1] = 1; U[n][1][2] = a % p;
        U[n][2][3] = 1; U[n][2][4] = a % p;
    }

    int PV[6][2][6], PU[6][2][6];
    for (int n = 0; n < 6; n++) {
        for (int r = 0; r < 2; r++) {
            for (int c = 0; c < 6; c++) {
                int sv = 0, su = 0;
                for (int t = 0; t < 3; t++) {
                    sv += A_sels[n][r][t] * V[n][t][c];
                    su += B_sels[n][r][t] * U[n][t][c];
                }
                PV[n][r][c] = mod_norm(sv, p);
                PU[n][r][c] = mod_norm(su, p);
            }
        }
    }

    /* Check all C(6,4) = 15 subsets for rank 12 desired and rank 8 interference */
    for (int i0 = 0; i0 < 6; i0++)
    for (int i1 = i0 + 1; i1 < 6; i1++)
    for (int i2 = i1 + 1; i2 < 6; i2++)
    for (int i3 = i2 + 1; i3 < 6; i3++) {
        int I[4] = {i0, i1, i2, i3};
        int Mdes[12 * 12];
        int Mint[8 * 12];
        for (int s = 0; s < 4; s++) {
            int n = I[s], a = alphas[n];
            for (int r = 0; r < 3; r++) {
                for (int c = 0; c < 6; c++) {
                    Mdes[(s * 3 + r) * 12 + c] = V[n][r][c];
                    Mdes[(s * 3 + r) * 12 + 6 + c] = (V[n][r][c] * a) % p;
                }
            }
            for (int r = 0; r < 2; r++) {
                for (int c = 0; c < 6; c++) {
                    Mint[(s * 2 + r) * 12 + c] = PU[n][r][c];
                    Mint[(s * 2 + r) * 12 + 6 + c] = (PU[n][r][c] * a) % p;
                }
            }
        }
        if (triad_rank_mod_p(Mdes, 12, 12, p) != 12) return false;
        if (triad_rank_mod_p(Mint, 8, 12, p) != 8) return false;
    }

    /* Check all 30 ordered pairs for exact single-orbit flag privacy (rank 5) */
    for (int i = 0; i < 6; i++) {
        for (int j = 0; j < 6; j++) {
            if (i == j) continue;
            int Mfv[5 * 6], Mfu[5 * 6];
            for (int r = 0; r < 2; r++)
                for (int c = 0; c < 6; c++) {
                    Mfv[r * 6 + c] = PV[i][r][c];
                    Mfu[r * 6 + c] = PU[i][r][c];
                }
            for (int r = 0; r < 3; r++)
                for (int c = 0; c < 6; c++) {
                    Mfv[(r + 2) * 6 + c] = V[j][r][c];
                    Mfu[(r + 2) * 6 + c] = U[j][r][c];
                }
            if (triad_rank_mod_p(Mfv, 5, 6, p) != 5) return false;
            if (triad_rank_mod_p(Mfu, 5, 6, p) != 5) return false;
        }
    }
    return true;
}

triad_chen_res_t triad_verify_chen_step9(int D, int c) {
    triad_chen_res_t res;
    res.D = D;
    res.c = c;
    res.max_even_mag = 0.0;
    res.max_odd_mag = 0.0;
    int N = 2 * D;
    for (int freq = 0; freq < N; freq++) {
        double re = 0.0, im = 0.0;
        for (int x = 0; x < N; x++) {
            double phi_f = M_PI * (double)c * (double)(x * x) / (double)D;
            double phi_w = -2.0 * M_PI * (double)(freq * x) / (double)N;
            double ang = phi_f + phi_w;
            re += cos(ang);
            im += sin(ang);
        }
        double mag = hypot(re, im);
        if (freq % 2 == 0) {
            if (mag > res.max_even_mag) res.max_even_mag = mag;
        } else {
            if (mag > res.max_odd_mag) res.max_odd_mag = mag;
        }
    }
    res.passed = (res.max_even_mag < 1e-11) && (res.max_odd_mag > 1.0);
    return res;
}

triad_qgtl_res_t triad_qgtl_shifted_lwe(int eta, double sigma, double e0) {
    triad_qgtl_res_t out;
    int support = 2 * eta + 1;
    double w[16], x[16], dlogp[16];
    double Z = 0.0;
    for (int k = 0; k < support; k++) {
        x[k] = (double)(k - eta);
        /* Use Gaussian-weighted or CBD-weighted amplitude */
        double arg = -(x[k] - e0) * (x[k] - e0) / (2.0 * sigma * sigma);
        w[k] = exp(arg);
        Z += w[k];
    }
    double ex = 0.0, ex2 = 0.0, eb = 0.0, eb2 = 0.0, exb = 0.0;
    double s3 = sigma * sigma * sigma;
    for (int k = 0; k < support; k++) {
        double p = w[k] / Z;
        double b = (x[k] - e0) * (x[k] - e0) / s3;
        dlogp[k] = 0.5 * b;
        ex += p * x[k];
        ex2 += p * x[k] * x[k];
        eb += p * b;
        eb2 += p * b * b;
        exb += p * x[k] * b;
    }
    (void)dlogp;
    double var_x = ex2 - ex * ex;
    double var_b = eb2 - eb * eb;
    double cov_xb = exb - ex * eb;

    /* Direct inner-product QGT computation:
     * |psi> = sum sqrt(p_x) e^{i theta x} |x>
     * |d_theta psi> = i x |psi>, |d_sigma psi> = (1/2)(b_x - E[b]) |psi>
     * Q_{theta, sigma} = <d_t psi | d_s psi> - <d_t psi | psi><psi | d_s psi>
     *                  = (-i/2) Cov(X, b(X))
     * => g_{ts} = Re(Q_{ts}) = 0, Omega_{ts} = -2 Im(Q_{ts}) = Cov(X, b(X))!
     */
    double q_im = 0.0, q_re = 0.0;
    for (int k = 0; k < support; k++) {
        double p = w[k] / Z;
        double b_cent = ((x[k] - e0) * (x[k] - e0) / s3) - eb;
        /* (-i * (x - ex)) * (0.5 * b_cent) * p */
        q_im += -0.5 * p * (x[k] - ex) * b_cent;
    }
    out.g_tt = var_x;
    out.g_ss = 0.25 * var_b;
    out.g_ts = q_re;
    out.omega_ts = -2.0 * q_im;
    out.cov_formula = cov_xb;
    out.max_err = fabs(out.omega_ts - out.cov_formula);
    return out;
}

static void cbd_pmf(int eta, double *probs, int *xs, int *len) {
    int n = 2 * eta;
    double denom = (double)(1 << n);
    *len = n + 1;
    for (int k = 0; k <= n; k++) {
        xs[k] = k - eta;
        probs[k] = (double)binom_small(n, k) / denom;
    }
}

static void eval_renyi(int eta, double sigma, double *out_r2, double *out_rinf) {
    double probs[16];
    int xs[16], len = 0;
    cbd_pmf(eta, probs, xs, &len);
    double two_s2 = 2.0 * sigma * sigma;
    double Z = 0.0;
    for (int x = -30; x <= 30; x++) {
        Z += exp(-(double)(x * x) / two_s2);
    }
    double r2 = 0.0, rinf = 0.0;
    for (int i = 0; i < len; i++) {
        double qx = exp(-(double)(xs[i] * xs[i]) / two_s2) / Z;
        r2 += (probs[i] * probs[i]) / qx;
        double ratio = probs[i] / qx;
        if (ratio > rinf) rinf = ratio;
    }
    *out_r2 = r2;
    *out_rinf = rinf;
}

triad_renyi_res_t triad_mlkem_renyi_opt(int eta) {
    triad_renyi_res_t res;
    res.eta = eta;
    res.min_r2 = 1e9;
    res.min_rinf = 1e9;
    res.sigma_opt_r2 = 1.0;
    res.sigma_opt_rinf = 1.0;
    /* Coarse grid then fine refinement */
    for (int step = 700; step <= 1800; step++) {
        double s = (double)step / 1000.0;
        double r2 = 0.0, rinf = 0.0;
        eval_renyi(eta, s, &r2, &rinf);
        if (r2 < res.min_r2) { res.min_r2 = r2; res.sigma_opt_r2 = s; }
        if (rinf < res.min_rinf) { res.min_rinf = rinf; res.sigma_opt_rinf = s; }
    }
    /* Fine golden-section refinement around sigma_opt_r2 */
    double lo = res.sigma_opt_r2 - 0.002, hi = res.sigma_opt_r2 + 0.002;
    for (int it = 0; it < 60; it++) {
        double m1 = lo + (hi - lo) / 3.0;
        double m2 = hi - (hi - lo) / 3.0;
        double r2_1, ri_1, r2_2, ri_2;
        eval_renyi(eta, m1, &r2_1, &ri_1);
        eval_renyi(eta, m2, &r2_2, &ri_2);
        if (r2_1 < r2_2) hi = m2; else lo = m1;
    }
    res.sigma_opt_r2 = 0.5 * (lo + hi);
    double dummy = 0.0;
    eval_renyi(eta, res.sigma_opt_r2, &res.min_r2, &dummy);
    res.bits_per_coord_r2 = log2(res.min_r2);
    return res;
}

int triad_mlkem_compress1(int x) {
    int xm = ((x % 3329) + 3329) % 3329;
    return ((2 * xm + 1665) / 3329) % 2;
}

/* Constant-time 1-byte sampler for Dyadic-256: w = (1,14,63,100,63,14,1)/256 on {-3..3}.
 * Cumulative buckets (256 outcomes):
 *   [0]       -> -3 (1)
 *   [1..14]   -> -2 (14)
 *   [15..77]  -> -1 (63)
 *   [78..177] ->  0 (100)
 *   [178..240]-> +1 (63)
 *   [241..254]-> +2 (14)
 *   [255]     -> +3 (1)
 */
int triad_dyadic256_sample_ct(uint8_t byte) {
    unsigned int b = (unsigned int)byte;
    int val = -3;
    val += (int)(b >= 1U);
    val += (int)(b >= 15U);
    val += (int)(b >= 78U);
    val += (int)(b >= 178U);
    val += (int)(b >= 241U);
    val += (int)(b >= 255U);
    return val;
}

static void eval_renyi_dyadic256(double sigma, double *out_r2, double *out_rinf) {
    static const int xs[7] = {-3, -2, -1, 0, 1, 2, 3};
    static const double probs[7] = {
        1.0 / 256.0, 14.0 / 256.0, 63.0 / 256.0, 100.0 / 256.0,
        63.0 / 256.0, 14.0 / 256.0, 1.0 / 256.0
    };
    double two_s2 = 2.0 * sigma * sigma;
    double Z = 0.0;
    for (int x = -30; x <= 30; x++) {
        Z += exp(-(double)(x * x) / two_s2);
    }
    double r2 = 0.0, rinf = 0.0;
    for (int i = 0; i < 7; i++) {
        double qx = exp(-(double)(xs[i] * xs[i]) / two_s2) / Z;
        r2 += (probs[i] * probs[i]) / qx;
        double ratio = probs[i] / qx;
        if (ratio > rinf) rinf = ratio;
    }
    *out_r2 = r2;
    *out_rinf = rinf;
}

triad_renyi_res_t triad_mlkem_dyadic256_opt(void) {
    triad_renyi_res_t res;
    res.eta = 256;
    res.min_r2 = 1e9;
    res.min_rinf = 1e9;
    res.sigma_opt_r2 = 1.0;
    res.sigma_opt_rinf = 1.0;
    for (int step = 800; step <= 1400; step++) {
        double s = (double)step / 1000.0;
        double r2 = 0.0, rinf = 0.0;
        eval_renyi_dyadic256(s, &r2, &rinf);
        if (r2 < res.min_r2) { res.min_r2 = r2; res.sigma_opt_r2 = s; }
        if (rinf < res.min_rinf) { res.min_rinf = rinf; res.sigma_opt_rinf = s; }
    }
    double lo = res.sigma_opt_r2 - 0.002, hi = res.sigma_opt_r2 + 0.002;
    for (int it = 0; it < 60; it++) {
        double m1 = lo + (hi - lo) / 3.0;
        double m2 = hi - (hi - lo) / 3.0;
        double r2_1, ri_1, r2_2, ri_2;
        eval_renyi_dyadic256(m1, &r2_1, &ri_1);
        eval_renyi_dyadic256(m2, &r2_2, &ri_2);
        if (r2_1 < r2_2) hi = m2; else lo = m1;
    }
    res.sigma_opt_r2 = 0.5 * (lo + hi);
    double dummy = 0.0;
    eval_renyi_dyadic256(res.sigma_opt_r2, &res.min_r2, &dummy);
    res.bits_per_coord_r2 = log2(res.min_r2);
    return res;
}

/* Constant-time 9-bit sampler for Dyadic-512: w = (1,8,44,120,166,120,44,8,1)/512 on {-4..4}.
 * Exact Var = 3/2 (matching FIPS 203 ML-KEM-512 CBD_3) and exact zero excess kurtosis (mu_4 = 27/4)! */
int triad_dyadic512_sample_ct(uint16_t raw9) {
    unsigned int r = (unsigned int)(raw9 & 511U);
    int val = -4;
    val += (int)(r >= 1U);
    val += (int)(r >= 9U);
    val += (int)(r >= 53U);
    val += (int)(r >= 173U);
    val += (int)(r >= 339U);
    val += (int)(r >= 459U);
    val += (int)(r >= 503U);
    val += (int)(r >= 511U);
    return val;
}

static void eval_renyi_dyadic512(double sigma, double *out_r2, double *out_rinf) {
    static const int xs[9] = {-4, -3, -2, -1, 0, 1, 2, 3, 4};
    static const double probs[9] = {
        1.0 / 512.0, 8.0 / 512.0, 44.0 / 512.0, 120.0 / 512.0, 166.0 / 512.0,
        120.0 / 512.0, 44.0 / 512.0, 8.0 / 512.0, 1.0 / 512.0
    };
    double two_s2 = 2.0 * sigma * sigma;
    double Z = 0.0;
    for (int x = -35; x <= 35; x++) {
        Z += exp(-(double)(x * x) / two_s2);
    }
    double r2 = 0.0, rinf = 0.0;
    for (int i = 0; i < 9; i++) {
        double qx = exp(-(double)(xs[i] * xs[i]) / two_s2) / Z;
        r2 += (probs[i] * probs[i]) / qx;
        double ratio = probs[i] / qx;
        if (ratio > rinf) rinf = ratio;
    }
    *out_r2 = r2;
    *out_rinf = rinf;
}

triad_renyi_res_t triad_mlkem_dyadic512_opt(void) {
    triad_renyi_res_t res;
    res.eta = 512;
    res.min_r2 = 1e9;
    res.min_rinf = 1e9;
    res.sigma_opt_r2 = 1.226;
    res.sigma_opt_rinf = 1.226;
    for (int step = 900; step <= 1600; step++) {
        double s = (double)step / 1000.0;
        double r2 = 0.0, rinf = 0.0;
        eval_renyi_dyadic512(s, &r2, &rinf);
        if (r2 < res.min_r2) { res.min_r2 = r2; res.sigma_opt_r2 = s; }
        if (rinf < res.min_rinf) { res.min_rinf = rinf; res.sigma_opt_rinf = s; }
    }
    double lo = res.sigma_opt_r2 - 0.002, hi = res.sigma_opt_r2 + 0.002;
    for (int it = 0; it < 60; it++) {
        double m1 = lo + (hi - lo) / 3.0;
        double m2 = hi - (hi - lo) / 3.0;
        double r2_1, ri_1, r2_2, ri_2;
        eval_renyi_dyadic512(m1, &r2_1, &ri_1);
        eval_renyi_dyadic512(m2, &r2_2, &ri_2);
        if (r2_1 < r2_2) hi = m2; else lo = m1;
    }
    res.sigma_opt_r2 = 0.5 * (lo + hi);
    double dummy = 0.0;
    eval_renyi_dyadic512(res.sigma_opt_r2, &res.min_r2, &dummy);
    res.bits_per_coord_r2 = log2(res.min_r2);
    return res;
}

bool triad_verify_twisted_dft(int m, int D, int r, double *out_max_forb) {
    if (m < 2 || D < 1 || m * D > 256) return false;
    int N = m * D;
    double fre[256], fim[256];
    for (int x = 0; x < N; x++) {
        int q = x / D;
        int rem = x % D;
        double base_ang = 0.7 * (double)(rem * rem) + 0.3 * (double)rem;
        double twist_ang = 2.0 * M_PI * (double)(q * r) / (double)m;
        fre[x] = cos(base_ang + twist_ang);
        fim[x] = sin(base_ang + twist_ang);
    }
    double max_forb = 0.0;
    for (int k = 0; k < N; k++) {
        double re = 0.0, im = 0.0;
        for (int x = 0; x < N; x++) {
            double ang = 2.0 * M_PI * (double)(k * x) / (double)N;
            double ca = cos(ang), sa = sin(ang);
            re += fre[x] * ca - fim[x] * sa;
            im += fre[x] * sa + fim[x] * ca;
        }
        if (((k + r) % m) != 0) {
            double mag = hypot(re, im);
            if (mag > max_forb) max_forb = mag;
        }
    }
    if (out_max_forb) *out_max_forb = max_forb;
    return max_forb < 1e-11;
}

bool triad_verify_koszul_flattening_certs(void) {
    /* 1. Verify 18-nonzero L_2 * Phi_1(<2,2,2>) = I_16 over Z (proves rank_F(<2,2,2>) >= 6) */
    static const int p4[6][2] = {{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}};
    int T2[4][4][4] = {{{0}}};
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++)
            for (int k = 0; k < 2; k++)
                T2[2*i+j][2*j+k][2*i+k] = 1;
    int M2[24][16] = {{0}};
    for (int row = 0; row < 24; row++) {
        int pi = row / 4, c = row % 4;
        int r0 = p4[pi][0], s0 = p4[pi][1];
        for (int col = 0; col < 16; col++) {
            int i = col / 4, b = col % 4;
            if (i == s0) M2[row][col] = T2[r0][b][c];
            else if (i == r0) M2[row][col] = -T2[s0][b][c];
        }
    }
    static const int L2_sp[18][3] = {
        {0,6,-1},{1,7,-1},{2,10,-1},{3,11,-1},{4,0,1},{4,10,-1},{5,1,1},{5,11,-1},
        {6,18,-1},{7,19,-1},{8,4,1},{9,5,1},{10,12,1},{11,13,1},{12,8,1},{13,9,1},{14,16,1},{15,17,1}
    };
    int L2[16][24] = {{0}};
    for (int t = 0; t < 18; t++) L2[L2_sp[t][0]][L2_sp[t][1]] = L2_sp[t][2];
    for (int i = 0; i < 16; i++) {
        for (int j = 0; j < 16; j++) {
            int acc = 0;
            for (int r = 0; r < 24; r++) acc += L2[i][r] * M2[r][j];
            if (acc != (i == j ? 1 : 0)) return false;
        }
    }

    /* 2. Verify 7-nonzero binary 3x3x3 tensor T_3 & 9x9 unimodular Z-inverse (proves rank_F(T_3) >= 5) */
    static const int p3[3][2] = {{0,1},{0,2},{1,2}};
    static const int T3_nz[7][3] = {{0,1,2},{0,2,1},{0,2,2},{1,0,2},{1,1,0},{2,0,1},{2,2,0}};
    int T3[3][3][3] = {{{0}}};
    for (int t = 0; t < 7; t++) T3[T3_nz[t][0]][T3_nz[t][1]][T3_nz[t][2]] = 1;
    int M3[9][9] = {{0}};
    for (int row = 0; row < 9; row++) {
        int pi = row / 3, c = row % 3;
        int r0 = p3[pi][0], s0 = p3[pi][1];
        for (int col = 0; col < 9; col++) {
            int i = col / 3, b = col % 3;
            if (i == s0) M3[row][col] = T3[r0][b][c];
            else if (i == r0) M3[row][col] = -T3[s0][b][c];
        }
    }
    static const int L3[9][9] = {
        { 0,-1, 0, 0,-1, 1,-1, 0, 0},
        {-1, 0, 0, 0, 0, 0, 0, 0, 0},
        { 0, 0, 0,-1, 0, 0, 0, 0, 0},
        { 0, 0, 0, 0, 0, 0, 0,-1, 0},
        { 0,-2, 1, 0,-1, 1,-1, 0, 0},
        { 0, 1, 0, 0, 0, 0, 0, 0, 0},
        { 0, 0, 0, 0, 0, 0, 0, 0, 1},
        { 0, 1, 0, 0, 0, 0, 1, 0, 0},
        { 0,-1, 0, 0, 0, 1,-1, 0, 0}
    };
    for (int i = 0; i < 9; i++) {
        for (int j = 0; j < 9; j++) {
            int acc = 0;
            for (int r = 0; r < 9; r++) acc += L3[i][r] * M3[r][j];
            if (acc != (i == j ? 1 : 0)) return false;
        }
    }
    return true;
}

bool triad_verify_strassen_7prod(void) {
    static const int U[7][4] = {
        { 1, 0, 0, 1}, { 0, 0, 1, 1}, { 1, 0, 0, 0}, { 0, 0, 0, 1},
        { 1, 1, 0, 0}, {-1, 0, 1, 0}, { 0, 1, 0,-1}
    };
    static const int V[7][4] = {
        { 1, 0, 0, 1}, { 1, 0, 0, 0}, { 0, 1, 0,-1}, {-1, 0, 1, 0},
        { 0, 0, 0, 1}, { 1, 1, 0, 0}, { 0, 0, 1, 1}
    };
    static const int W[7][4] = {
        { 1, 0, 0, 1}, { 0, 0, 1,-1}, { 0, 1, 0, 1}, { 1, 0, 1, 0},
        {-1, 1, 0, 0}, { 0, 0, 0, 1}, { 1, 0, 0, 0}
    };
    for (int a = 0; a < 4; a++) {
        for (int b = 0; b < 4; b++) {
            for (int c = 0; c < 4; c++) {
                int acc = 0;
                for (int s = 0; s < 7; s++) acc += U[s][a] * V[s][b] * W[s][c];
                int expected = ((a / 2 == c / 2) && (a % 2 == b / 2) && (b % 2 == c % 2)) ? 1 : 0;
                if (acc != expected) return false;
            }
        }
    }
    return true;
}

bool triad_verify_all_m_koszul_monomial(int m) {
    if (m < 2 || m > 5) return false;
    int n = m * m;
    int dim = n * n;
    for (int i = 0; i < dim; i++) {
        int a = i / n, b = i % n;
        int p = (((a / m) + 1) % m) * m + (b / m);
        int c0 = (((a / m) + 1) % m) * m + (b % m);
        int r0 = (p < a) ? p : a;
        int s0 = (p < a) ? a : p;
        int sgn = (p < a) ? 1 : -1;
        for (int j = 0; j < dim; j++) {
            int ja = j / n, jb = j % n;
            int phi = 0;
            if (ja == s0) {
                phi = ((r0 / m == c0 / m) && (r0 % m == jb / m) && (jb % m == c0 % m)) ? 1 : 0;
            } else if (ja == r0) {
                phi = -(((s0 / m == c0 / m) && (s0 % m == jb / m) && (jb % m == c0 % m)) ? 1 : 0);
            }
            if (sgn * phi != (i == j ? 1 : 0)) return false;
        }
    }
    return true;
}
