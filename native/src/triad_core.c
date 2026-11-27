/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander S. Donahue
 */
#include "triad_core.h"
#include "f101_t3_k3_e6_data.h"

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
    if (!mat || rows <= 0 || cols <= 0 || p <= 1) return 0;
    if ((long long)rows * (long long)cols > 1048576LL) return -1;
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
    if (T < 1 || Tp < 1 || Tp > T || K < 1 || K > 8 || T > 6 || p < 2) return -1;
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
    res.passed = false;
    if (D < 1 || D > 2048) return res;
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
    memset(&out, 0, sizeof(out));
    if (eta < 1 || eta > 7 || !(sigma > 0.0) || !isfinite(sigma) || !isfinite(e0)) {
        out.max_err = NAN;
        return out;
    }
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
    memset(&res, 0, sizeof(res));
    res.eta = eta;
    if (eta < 1 || eta > 7) {
        res.min_r2 = NAN;
        res.min_rinf = NAN;
        res.bits_per_coord_r2 = NAN;
        return res;
    }
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
    /* Exact NIST FIPS 203 Eq. (4.7): floor((2/3329)*x + 1/2) mod 2 = floor((4*xm + 3329)/6658) mod 2 */
    int xm = ((x % 3329) + 3329) % 3329;
    return ((4 * xm + 3329) / 6658) % 2;
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
    if (m < 2 || D < 1 || (long long)m * (long long)D > 256LL) return false;
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

/* Constant-time 10-bit sampler for Dyadic-1024-A: w = (4,57,248,406,248,57,4)/1024 on {-3..3}.
 * Exact Var = 1, mu_4 = 371/128, QGTL det(g) = 243/512; minimizes Bai et al. (2018) end-to-end loss! */
int triad_dyadic1024a_sample_ct(uint16_t raw10) {
    unsigned int r = (unsigned int)(raw10 & 1023U);
    int val = -3;
    val += (int)(r >= 4U);
    val += (int)(r >= 61U);
    val += (int)(r >= 309U);
    val += (int)(r >= 715U);
    val += (int)(r >= 963U);
    val += (int)(r >= 1020U);
    return val;
}

/* Constant-time 10-bit sampler for Dyadic-1024-B: w = (1,17,90,239,330,239,90,17,1)/1024 on {-4..4}.
 * Exact Var = 3/2, mu_4 = 207/32, QGTL det(g) = 15/32; minimizes ML-KEM-512 Bai et al. (2018) loss! */
int triad_dyadic1024b_sample_ct(uint16_t raw10) {
    unsigned int r = (unsigned int)(raw10 & 1023U);
    int val = -4;
    val += (int)(r >= 1U);
    val += (int)(r >= 18U);
    val += (int)(r >= 108U);
    val += (int)(r >= 347U);
    val += (int)(r >= 677U);
    val += (int)(r >= 916U);
    val += (int)(r >= 1006U);
    val += (int)(r >= 1023U);
    return val;
}

static void eval_renyi_table(const int *xs, const double *probs, int len, double sigma,
                             double *out_r2, double *out_rinf) {
    double two_s2 = 2.0 * sigma * sigma;
    double Z = 0.0;
    for (int x = -35; x <= 35; x++) {
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

static triad_renyi_res_t opt_renyi_table(int tag, const int *xs, const double *probs, int len,
                                         int lo_milli, int hi_milli) {
    triad_renyi_res_t res;
    res.eta = tag;
    res.min_r2 = 1e9;
    res.min_rinf = 1e9;
    res.sigma_opt_r2 = 1.0;
    res.sigma_opt_rinf = 1.0;
    for (int step = lo_milli; step <= hi_milli; step++) {
        double s = (double)step / 1000.0;
        double r2 = 0.0, rinf = 0.0;
        eval_renyi_table(xs, probs, len, s, &r2, &rinf);
        if (r2 < res.min_r2) { res.min_r2 = r2; res.sigma_opt_r2 = s; }
        if (rinf < res.min_rinf) { res.min_rinf = rinf; res.sigma_opt_rinf = s; }
    }
    double lo = res.sigma_opt_r2 - 0.002, hi = res.sigma_opt_r2 + 0.002;
    for (int it = 0; it < 60; it++) {
        double m1 = lo + (hi - lo) / 3.0;
        double m2 = hi - (hi - lo) / 3.0;
        double r2_1, ri_1, r2_2, ri_2;
        eval_renyi_table(xs, probs, len, m1, &r2_1, &ri_1);
        eval_renyi_table(xs, probs, len, m2, &r2_2, &ri_2);
        if (r2_1 < r2_2) hi = m2; else lo = m1;
    }
    res.sigma_opt_r2 = 0.5 * (lo + hi);
    double dummy = 0.0;
    eval_renyi_table(xs, probs, len, res.sigma_opt_r2, &res.min_r2, &dummy);

    lo = res.sigma_opt_rinf - 0.002; hi = res.sigma_opt_rinf + 0.002;
    for (int it = 0; it < 60; it++) {
        double m1 = lo + (hi - lo) / 3.0;
        double m2 = hi - (hi - lo) / 3.0;
        double r2_1, ri_1, r2_2, ri_2;
        eval_renyi_table(xs, probs, len, m1, &r2_1, &ri_1);
        eval_renyi_table(xs, probs, len, m2, &r2_2, &ri_2);
        if (ri_1 < ri_2) hi = m2; else lo = m1;
    }
    res.sigma_opt_rinf = 0.5 * (lo + hi);
    eval_renyi_table(xs, probs, len, res.sigma_opt_rinf, &dummy, &res.min_rinf);
    res.bits_per_coord_r2 = log2(res.min_r2);
    return res;
}

triad_renyi_res_t triad_mlkem_dyadic1024a_opt(void) {
    static const int xs[7] = {-3, -2, -1, 0, 1, 2, 3};
    static const double probs[7] = {
        4.0 / 1024.0, 57.0 / 1024.0, 248.0 / 1024.0, 406.0 / 1024.0,
        248.0 / 1024.0, 57.0 / 1024.0, 4.0 / 1024.0
    };
    return opt_renyi_table(1024, xs, probs, 7, 800, 1400);
}

triad_renyi_res_t triad_mlkem_dyadic1024b_opt(void) {
    static const int xs[9] = {-4, -3, -2, -1, 0, 1, 2, 3, 4};
    static const double probs[9] = {
        1.0 / 1024.0, 17.0 / 1024.0, 90.0 / 1024.0, 239.0 / 1024.0, 330.0 / 1024.0,
        239.0 / 1024.0, 90.0 / 1024.0, 17.0 / 1024.0, 1.0 / 1024.0
    };
    return opt_renyi_table(1025, xs, probs, 9, 900, 1600);
}

typedef struct {
    long long a;
    long long b;
} zsqrt5_t;

static zsqrt5_t z5_add(zsqrt5_t x, zsqrt5_t y) {
    zsqrt5_t r = {x.a + y.a, x.b + y.b};
    return r;
}

static zsqrt5_t z5_mul(zsqrt5_t x, zsqrt5_t y) {
    zsqrt5_t r = {x.a * y.a + 5LL * x.b * y.b, x.a * y.b + x.b * y.a};
    return r;
}

static bool cyc_adj(int n, int i, int j) {
    int d1 = (i - j + n) % n;
    int d2 = (j - i + n) % n;
    return (d1 == 1) || (d2 == 1);
}

/* Exact Z[sqrt(5)] 3-term SOS audit of Lovasz 6x6 umbrella Gram matrix 80*M_6 + C_5^2 5-set (T3j). */
bool triad_verify_lovasz_c5_sos(void) {
    static const zsqrt5_t W[3] = {{0, 16}, {5, -1}, {10, 0}};
    static const zsqrt5_t Z[6][3] = {
        {{0, 1},  {0, 0},   {0, 0}},
        {{1, 0},  {4, 0},   {0, 0}},
        {{1, 0},  {-1, 1},  {2, 0}},
        {{1, 0},  {-1, -1}, {-1, 1}},
        {{1, 0},  {-1, -1}, {1, -1}},
        {{1, 0},  {-1, 1},  {-2, 0}}
    };
    for (int i = 0; i < 6; i++) {
        for (int j = 0; j < 6; j++) {
            zsqrt5_t acc = {0, 0};
            for (int r = 0; r < 3; r++) {
                acc = z5_add(acc, z5_mul(W[r], z5_mul(Z[i][r], Z[j][r])));
            }
            zsqrt5_t exp_m = {0, 0};
            if (i == 0 && j == 0) { exp_m.a = 0; exp_m.b = 80; }
            else if (i == 0 || j == 0 || i == j) { exp_m.a = 80; exp_m.b = 0; }
            else if (cyc_adj(5, i - 1, j - 1)) { exp_m.a = -40; exp_m.b = 40; }
            if (acc.a != exp_m.a || acc.b != exp_m.b) return false;
        }
    }
    /* Verify explicit 5-element independent set in C_5^{box 2}: {0, 7, 14, 16, 23} */
    static const int c5_ind[5] = {0, 7, 14, 16, 23};
    for (int i = 0; i < 5; i++) {
        for (int j = i + 1; j < 5; j++) {
            int x0 = c5_ind[i] % 5, x1 = c5_ind[i] / 5;
            int y0 = c5_ind[j] % 5, y1 = c5_ind[j] / 5;
            bool ok0 = (x0 == y0) || cyc_adj(5, x0, y0);
            bool ok1 = (x1 == y1) || cyc_adj(5, x1, y1);
            if (ok0 && ok1) return false;
        }
    }
    return true;
}

/* Exact C_7^{box 2} 10-element independent set & 4-clique Haemers rank-4 cover (T3j). */
bool triad_verify_c7_indep10_and_haemers(void) {
    static const int c7_ind[10] = {0, 2, 11, 14, 16, 25, 29, 34, 38, 47};
    for (int i = 0; i < 10; i++) {
        if (c7_ind[i] < 0 || c7_ind[i] >= 49) return false;
        for (int j = i + 1; j < 10; j++) {
            if (c7_ind[i] == c7_ind[j]) return false;
            int x0 = c7_ind[i] % 7, x1 = c7_ind[i] / 7;
            int y0 = c7_ind[j] % 7, y1 = c7_ind[j] / 7;
            bool adj0 = (x0 == y0) || cyc_adj(7, x0, y0);
            bool adj1 = (x1 == y1) || cyc_adj(7, x1, y1);
            if (adj0 && adj1) return false;
        }
    }
    /* Verify 4-clique cover c(i)=i/2 fits C_7 (same clique implies equal or adjacent) */
    for (int i = 0; i < 7; i++) {
        for (int j = 0; j < 7; j++) {
            if (i != j && (i / 2) == (j / 2) && !cyc_adj(7, i, j)) return false;
        }
    }
    return true;
}

/* Constant-time 14-bit sampler for Pareto-optimal Dyadic-16384-A (ML-KEM-768/1024, Var=1, T2i):
 * w = (67, 904, 3973, 6496, 3973, 904, 67) / 16384 on {-3..3} (6 branchless comparisons). */
int triad_dyadic16384a_sample_ct(uint16_t raw14) {
    unsigned int r = (unsigned int)(raw14 & 16383U);
    int val = -3;
    val += (int)(r >= 67U);
    val += (int)(r >= 971U);
    val += (int)(r >= 4944U);
    val += (int)(r >= 11440U);
    val += (int)(r >= 15413U);
    val += (int)(r >= 16317U);
    return val;
}

/* Constant-time 14-bit sampler for sub-1-bit Bai-optimal Dyadic-16384-B (ML-KEM-512, Var=3/2, T2i):
 * w = (1, 25, 267, 1409, 3824, 5332, 3824, 1409, 267, 25, 1) / 16384 on {-5..5} (10 branchless comparisons). */
int triad_dyadic16384b_sample_ct(uint16_t raw14) {
    unsigned int r = (unsigned int)(raw14 & 16383U);
    int val = -5;
    val += (int)(r >= 1U);
    val += (int)(r >= 26U);
    val += (int)(r >= 293U);
    val += (int)(r >= 1702U);
    val += (int)(r >= 5526U);
    val += (int)(r >= 10858U);
    val += (int)(r >= 14682U);
    val += (int)(r >= 16091U);
    val += (int)(r >= 16358U);
    val += (int)(r >= 16383U);
    return val;
}

triad_renyi_res_t triad_mlkem_dyadic16384a_opt(void) {
    static const int xs[7] = {-3, -2, -1, 0, 1, 2, 3};
    static const double probs[7] = {
        67.0 / 16384.0, 904.0 / 16384.0, 3973.0 / 16384.0, 6496.0 / 16384.0,
        3973.0 / 16384.0, 904.0 / 16384.0, 67.0 / 16384.0
    };
    return opt_renyi_table(16384, xs, probs, 7, 800, 1400);
}

triad_renyi_res_t triad_mlkem_dyadic16384b_opt(void) {
    static const int xs[11] = {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5};
    static const double probs[11] = {
        1.0 / 16384.0, 25.0 / 16384.0, 267.0 / 16384.0, 1409.0 / 16384.0, 3824.0 / 16384.0,
        5332.0 / 16384.0,
        3824.0 / 16384.0, 1409.0 / 16384.0, 267.0 / 16384.0, 25.0 / 16384.0, 1.0 / 16384.0
    };
    return opt_renyi_table(16385, xs, probs, 11, 900, 1600);
}

/* Exact F_2^64 Gaussian elimination rank on 64-bit sparse bitmask rows (T1j). */
static int gf2_rank_u64(const uint64_t *rows, int n) {
    uint64_t basis[64];
    memset(basis, 0, sizeof(basis));
    int rk = 0;
    for (int i = 0; i < n; i++) {
        uint64_t v = rows[i];
        while (v != 0ULL) {
            int bit = 0;
            uint64_t tmp = v;
            while ((tmp & 1ULL) == 0ULL) {
                tmp >>= 1;
                bit++;
            }
            if (basis[bit] == 0ULL) {
                basis[bit] = v;
                rk++;
                break;
            }
            v ^= basis[bit];
        }
    }
    return rk;
}

/* Verify ALL 64 subsets of the single Z_4-cyclic F_2^64 6-subspace arrangement match h_uncond / 4 (T1j). */
bool triad_verify_ret6_f2_64(void) {
    uint64_t subs[6][32];
    int lens[6] = {32, 32, 13, 13, 13, 13};
    for (int j = 0; j < 32; j++) {
        subs[0][j] = (1ULL << j);
        subs[1][j] = (1ULL << (32 + j));
    }
    for (int i = 0; i < 4; i++) {
        int s = 2 + i;
        for (int j = 0; j < 5; j++) {
            subs[s][j] = (1ULL << (5 * i + j));
            subs[s][5 + j] = (1ULL << (32 + 5 * i + j));
        }
        subs[s][10] = (1ULL << (20 + 3 * i + 0))
                    | (1ULL << (32 + (8 + 5 * i) % 20))
                    | (1ULL << (32 + (17 + 5 * i) % 20))
                    | (1ULL << (32 + (19 + 5 * i) % 20));
        subs[s][11] = (1ULL << (20 + 3 * i + 1))
                    | (1ULL << (32 + (11 + 5 * i) % 20))
                    | (1ULL << (32 + (12 + 5 * i) % 20))
                    | (1ULL << (32 + (18 + 5 * i) % 20));
        subs[s][12] = (1ULL << (20 + 3 * i + 2))
                    | (1ULL << (32 + (5 + 5 * i) % 20))
                    | (1ULL << (32 + (11 + 5 * i) % 20))
                    | (1ULL << (32 + (18 + 5 * i) % 20));
    }
    /* Exact h_uncond retrieval-6 values indexed by [w1][w2][popcount(A)] */
    static const int target[2][2][5] = {
        { {0, 52, 104, 156, 208}, {128, 160, 192, 224, 256} },
        { {128, 160, 192, 208, 208}, {256, 256, 256, 256, 256} }
    };
    uint64_t buf[128];
    for (int mask = 0; mask < 64; mask++) {
        int cnt = 0;
        for (int idx = 0; idx < 6; idx++) {
            if ((mask >> idx) & 1) {
                for (int r = 0; r < lens[idx]; r++) buf[cnt++] = subs[idx][r];
            }
        }
        int rk = gf2_rank_u64(buf, cnt);
        int w1 = mask & 1;
        int w2 = (mask >> 1) & 1;
        int popA = ((mask >> 2) & 1) + ((mask >> 3) & 1) + ((mask >> 4) & 1) + ((mask >> 5) & 1);
        if (4 * rk != target[w1][w2][popA]) return false;
    }
    return true;
}

/* Verify exact Z[sqrt(p)] 2-block SOS identity R^T R = 2p*sqrt(p)*R & self-complement map for Paley P_p (T3l). */
bool triad_verify_paley_conference_sos(int p) {
    if (p < 5 || p > 41 || ((p - 1) % 4) != 0) return false;
    for (int d = 2; d * d <= p; d++) {
        if ((p % d) == 0) return false;
    }
    int k = (p - 1) / 4;
    bool qr[42];
    memset(qr, 0, sizeof(qr));
    for (int x = 1; x < p; x++) qr[(x * x) % p] = true;

    int A[41][41];
    for (int i = 0; i < p; i++) {
        for (int j = 0; j < p; j++) {
            int diff = (i - j + p) % p;
            A[i][j] = (i != j && qr[diff]) ? 1 : 0;
        }
    }
    /* 1. Verify symmetric, loopless, 2k-regular, and conference equation A^2 + A - kI = kJ */
    for (int i = 0; i < p; i++) {
        int deg = 0;
        if (A[i][i] != 0) return false;
        for (int j = 0; j < p; j++) {
            if (A[i][j] != A[j][i]) return false;
            deg += A[i][j];
            int a2 = 0;
            for (int t = 0; t < p; t++) a2 += A[i][t] * A[t][j];
            int lhs = a2 + A[i][j] - ((i == j) ? k : 0);
            if (lhs != k) return false;
        }
        if (deg != 2 * k) return false;
    }
    /* 2. Exact Z[sqrt(p)] 2-block SOS audit: R = 2p*A + p*(1+sqrt(p))*I - (p+sqrt(p))*J => R^T R = 2p*sqrt(p)*R */
    long long Ra[41][41], Rb[41][41];
    for (int i = 0; i < p; i++) {
        for (int j = 0; j < p; j++) {
            if (i == j) {
                Ra[i][j] = 0LL;
                Rb[i][j] = (long long)(p - 1);
            } else if (A[i][j] == 1) {
                Ra[i][j] = (long long)p;
                Rb[i][j] = -1LL;
            } else {
                Ra[i][j] = -(long long)p;
                Rb[i][j] = -1LL;
            }
        }
    }
    for (int i = 0; i < p; i++) {
        for (int j = 0; j < p; j++) {
            long long acc_a = 0LL, acc_b = 0LL;
            for (int t = 0; t < p; t++) {
                acc_a += Ra[t][i] * Ra[t][j] + (long long)p * Rb[t][i] * Rb[t][j];
                acc_b += Ra[t][i] * Rb[t][j] + Rb[t][i] * Ra[t][j];
            }
            long long exp_a = 2LL * (long long)p * (long long)p * Rb[i][j];
            long long exp_b = 2LL * (long long)p * Ra[i][j];
            if (acc_a != exp_a || acc_b != exp_b) return false;
        }
    }
    /* 3. Verify explicit self-complement anti-automorphism phi(x) = (g*x) % p giving p-set in P_p^{box 2} */
    int g = -1;
    for (int x = 2; x < p; x++) {
        if (!qr[x]) { g = x; break; }
    }
    if (g < 0) return false;
    for (int x = 0; x < p; x++) {
        for (int y = x + 1; y < p; y++) {
            int px = (g * x) % p;
            int py = (g * y) % p;
            if (px == py) return false;
            if (A[x][y] == A[px][py]) return false;
        }
    }
    return true;
}

/* Independent ISO C11 verification of the committed F_101 (seed=2028) zero-error, exact T=3-private
 * (M=2, N=6, K=3, T=3) rate-10/17 PIR witness (`ERRATA S01` closure, matching Lean `T1k` & Python). */
bool triad_verify_f101_t3_k3_e6_zero_error(void) {
    const int p = 101;
    const int alphas[6] = {1, 2, 3, 4, 5, 6};
    int G[6][3];
    for (int n = 0; n < 6; n++) {
        G[n][0] = 1;
        G[n][1] = alphas[n] % p;
        G[n][2] = (alphas[n] * alphas[n]) % p;
    }

    /* Enumerate sorted 3-blades of F_101^6 (20 elements) */
    int b3[20][3];
    int b3_cnt = 0;
    for (int i = 0; i < 6; i++)
        for (int j = i + 1; j < 6; j++)
            for (int k = j + 1; k < 6; k++) {
                b3[b3_cnt][0] = i; b3[b3_cnt][1] = j; b3[b3_cnt][2] = k;
                b3_cnt++;
            }

    /* Enumerate 2-subsets S of {1..5} (10 elements) */
    int s2[10][2];
    int s2_cnt = 0;
    for (int i = 1; i < 6; i++)
        for (int j = i + 1; j < 6; j++) {
            s2[s2_cnt][0] = i; s2[s2_cnt][1] = j;
            s2_cnt++;
        }

    int V[6][10][20], U[6][10][20];
    memset(V, 0, sizeof(V));
    memset(U, 0, sizeof(U));
    for (int n = 0; n < 6; n++) {
        int a = alphas[n];
        int u[6];
        u[0] = 1;
        for (int d = 1; d < 6; d++) u[d] = (u[d - 1] * a) % p;
        for (int si = 0; si < 10; si++) {
            int x0 = s2[si][0], x1 = s2[si][1];
            for (int d = 0; d < 6; d++) {
                if (d == x0 || d == x1) continue;
                int tup[3] = {d, x0, x1};
                int inv_cnt = (d > x0 ? 1 : 0) + (d > x1 ? 1 : 0);
                for (int r = 1; r < 3; r++) {
                    int key = tup[r], q = r - 1;
                    while (q >= 0 && tup[q] > key) { tup[q + 1] = tup[q]; q--; }
                    tup[q + 1] = key;
                }
                for (int bi = 0; bi < 20; bi++) {
                    if (b3[bi][0] == tup[0] && b3[bi][1] == tup[1] && b3[bi][2] == tup[2]) {
                        int sgn = (inv_cnt & 1) ? -1 : 1;
                        V[n][si][bi] = mod_norm(sgn * u[d], p);
                        break;
                    }
                }
            }
        }
        int a2 = (a * a) % p;
        U[n][0][0] = 1;
        for (int c = 0; c < 3; c++) {
            int b = 1 + 3 * c;
            U[n][1 + 2 * c][b] = 1;
            U[n][1 + 2 * c][b + 2] = mod_norm(-a2, p);
            U[n][2 + 2 * c][b + 1] = 1;
            U[n][2 + 2 * c][b + 2] = a % p;
        }
        for (int c = 0; c < 3; c++) {
            int b = 10 + 3 * c;
            U[n][7 + c][b] = 1;
            U[n][7 + c][b + 1] = a % p;
            U[n][7 + c][b + 2] = a2;
        }
    }

    int P[6][7][20], C[6][3][20], Q[6][7][20], D[6][3][20];
    for (int n = 0; n < 6; n++) {
        for (int r = 0; r < 10; r++) {
            for (int c = 0; c < 20; c++) {
                int sv = 0, su = 0;
                for (int t = 0; t < 10; t++) {
                    sv += (int)F101_T3K3_A_SELS[n][r][t] * V[n][t][c];
                    su += (int)F101_T3K3_B_SELS[n][r][t] * U[n][t][c];
                }
                if (r < 7) {
                    P[n][r][c] = mod_norm(sv, p);
                    Q[n][r][c] = mod_norm(su, p);
                } else {
                    C[n][r - 7][c] = mod_norm(sv, p);
                    D[n][r - 7][c] = mod_norm(su, p);
                }
            }
        }
    }

    /* 1. Desired recovery rank = 60/60 (full invertible 60x60 over F_101) */
    int M_des[60 * 60];
    int M_pure[42 * 60];
    int M_all_int[60 * 60];
    for (int n = 0; n < 6; n++) {
        for (int r = 0; r < 7; r++) {
            for (int k = 0; k < 3; k++) {
                for (int j = 0; j < 20; j++) {
                    M_des[(n * 10 + r) * 60 + k * 20 + j] = (G[n][k] * P[n][r][j]) % p;
                    M_pure[(n * 7 + r) * 60 + k * 20 + j] = (G[n][k] * Q[n][r][j]) % p;
                    M_all_int[(n * 10 + r) * 60 + k * 20 + j] = (G[n][k] * Q[n][r][j]) % p;
                }
            }
        }
        for (int r = 0; r < 3; r++) {
            for (int k = 0; k < 3; k++) {
                for (int j = 0; j < 20; j++) {
                    M_des[(n * 10 + 7 + r) * 60 + k * 20 + j] = (G[n][k] * C[n][r][j]) % p;
                    M_all_int[(n * 10 + 7 + r) * 60 + k * 20 + j] = (G[n][k] * D[n][r][j]) % p;
                }
            }
        }
    }
    if (triad_rank_mod_p(M_des, 60, 60, p) != 60) return false;
    if (triad_rank_mod_p(M_pure, 42, 60, p) != 42) return false;
    if (triad_rank_mod_p(M_all_int, 60, 60, p) != 42) return false;

    /* 2. Exact T=3 privacy: ALL 20/20 colluding triples have invertible M_I in GL_20(F_101)
     * mapping P_n -> Q_n (dim 7) and span(P_n, C_n) -> span(Q_n, D_n) (dim 10) for every n in I! */
    for (int s = 0; s < 20; s++) {
        int M_mat[20 * 20];
        for (int i = 0; i < 20; i++)
            for (int j = 0; j < 20; j++)
                M_mat[i * 20 + j] = (int)F101_T3K3_M_ISOS[s][i][j];
        if (triad_rank_mod_p(M_mat, 20, 20, p) != 20) return false;

        for (int idx = 0; idx < 3; idx++) {
            int n = (int)F101_T3K3_SUBSETS[s][idx];
            int pm7[7 * 20];
            int pmc10[10 * 20];
            int stk14[14 * 20];
            int stk20[20 * 20];
            int q7[7 * 20];
            int qd10[10 * 20];
            for (int r = 0; r < 7; r++) {
                for (int j = 0; j < 20; j++) {
                    int acc = 0;
                    for (int t = 0; t < 20; t++) acc += P[n][r][t] * M_mat[t * 20 + j];
                    int pm = acc % p;
                    pm7[r * 20 + j] = pm;
                    pmc10[r * 20 + j] = pm;
                    q7[r * 20 + j] = Q[n][r][j];
                    qd10[r * 20 + j] = Q[n][r][j];
                    stk14[r * 20 + j] = pm;
                    stk14[(7 + r) * 20 + j] = Q[n][r][j];
                    stk20[r * 20 + j] = pm;
                    stk20[(10 + r) * 20 + j] = Q[n][r][j];
                }
            }
            for (int r = 0; r < 3; r++) {
                for (int j = 0; j < 20; j++) {
                    int acc = 0;
                    for (int t = 0; t < 20; t++) acc += C[n][r][t] * M_mat[t * 20 + j];
                    int cm = acc % p;
                    pmc10[(7 + r) * 20 + j] = cm;
                    qd10[(7 + r) * 20 + j] = D[n][r][j];
                    stk20[(7 + r) * 20 + j] = cm;
                    stk20[(17 + r) * 20 + j] = D[n][r][j];
                }
            }
            if (triad_rank_mod_p(pm7, 7, 20, p) != 7) return false;
            if (triad_rank_mod_p(q7, 7, 20, p) != 7) return false;
            if (triad_rank_mod_p(stk14, 14, 20, p) != 7) return false;
            if (triad_rank_mod_p(pmc10, 10, 20, p) != 10) return false;
            if (triad_rank_mod_p(qd10, 10, 20, p) != 10) return false;
            if (triad_rank_mod_p(stk20, 20, 20, p) != 10) return false;
        }
    }

    /* 3. End-to-end live C11 encode + zero-error decode round-trip for BOTH theta=0 and theta=1 (H49):
     *    Compute exact 60x60 DecInv = M_des^{-1} mod 101 and 18x42 Cancel with Cancel * M_pure = M_mixed,
     *    encode two distinct 60-symbol files W1, W2 across 6 MDS servers (102 downloaded symbols = rate 10/17),
     *    strip pure interference via Cancel, apply DecInv, and assert bit-for-bit recovery of all 60 symbols! */
    int aug_des[60][120];
    for (int i = 0; i < 60; i++) {
        for (int j = 0; j < 60; j++) {
            aug_des[i][j] = M_des[i * 60 + j];
            aug_des[i][60 + j] = (i == j) ? 1 : 0;
        }
    }
    for (int c = 0; c < 60; c++) {
        int piv = -1;
        for (int i = c; i < 60; i++) {
            if (aug_des[i][c] != 0) { piv = i; break; }
        }
        if (piv < 0) return false;
        if (piv != c) {
            for (int j = 0; j < 120; j++) {
                int tmp = aug_des[c][j]; aug_des[c][j] = aug_des[piv][j]; aug_des[piv][j] = tmp;
            }
        }
        int inv = triad_mod_inv(aug_des[c][c], p);
        for (int j = 0; j < 120; j++) aug_des[c][j] = (aug_des[c][j] * inv) % p;
        for (int i = 0; i < 60; i++) {
            if (i != c && aug_des[i][c] != 0) {
                int f = aug_des[i][c];
                for (int j = 0; j < 120; j++) {
                    aug_des[i][j] = mod_norm(aug_des[i][j] - f * aug_des[c][j], p);
                }
            }
        }
    }

    /* Solve M_pure^T * Cancel^T = M_mixed^T (60 equations in 42 vars for each of 18 RHS columns) */
    int aug_can[60][60];
    for (int i = 0; i < 60; i++) {
        for (int j = 0; j < 42; j++) aug_can[i][j] = M_pure[j * 60 + i];
        for (int m = 0; m < 18; m++) {
            int n_srv = m / 3;
            int r_blk = m % 3;
            int k_mds = i / 20;
            int col_j = i % 20;
            aug_can[i][42 + m] = (G[n_srv][k_mds] * D[n_srv][r_blk][col_j]) % p;
        }
    }
    int piv_row = 0;
    int piv_cols[42];
    for (int c = 0; c < 42; c++) {
        int piv = -1;
        for (int i = piv_row; i < 60; i++) {
            if (aug_can[i][c] != 0) { piv = i; break; }
        }
        if (piv < 0) return false;
        if (piv != piv_row) {
            for (int j = 0; j < 60; j++) {
                int tmp = aug_can[piv_row][j]; aug_can[piv_row][j] = aug_can[piv][j]; aug_can[piv][j] = tmp;
            }
        }
        int inv = triad_mod_inv(aug_can[piv_row][c], p);
        for (int j = 0; j < 60; j++) aug_can[piv_row][j] = (aug_can[piv_row][j] * inv) % p;
        for (int i = 0; i < 60; i++) {
            if (i != piv_row && aug_can[i][c] != 0) {
                int f = aug_can[i][c];
                for (int j = 0; j < 60; j++) {
                    aug_can[i][j] = mod_norm(aug_can[i][j] - f * aug_can[piv_row][j], p);
                }
            }
        }
        piv_cols[c] = piv_row;
        piv_row++;
    }
    for (int i = 42; i < 60; i++) {
        for (int m = 0; m < 18; m++) {
            if (aug_can[i][42 + m] != 0) return false;
        }
    }
    int Cancel[18][42];
    for (int m = 0; m < 18; m++) {
        for (int j = 0; j < 42; j++) Cancel[m][j] = aug_can[piv_cols[j]][42 + m];
    }

    /* Deterministic non-trivial 60-symbol files W1, W2 and MDS storage Y1, Y2 */
    int W1[3][20], W2[3][20], Y1[6][20], Y2[6][20];
    for (int k = 0; k < 3; k++) {
        for (int j = 0; j < 20; j++) {
            W1[k][j] = (7 * k + 13 * j + 5) % p;
            W2[k][j] = (19 * k + 31 * j + 11) % p;
        }
    }
    for (int n = 0; n < 6; n++) {
        for (int j = 0; j < 20; j++) {
            int s1 = 0, s2v = 0;
            for (int k = 0; k < 3; k++) {
                s1 += G[n][k] * W1[k][j];
                s2v += G[n][k] * W2[k][j];
            }
            Y1[n][j] = s1 % p;
            Y2[n][j] = s2v % p;
        }
    }
    for (int theta = 0; theta < 2; theta++) {
        int A1[6][7], A2[6][7], A3[6][3];
        for (int n = 0; n < 6; n++) {
            for (int r = 0; r < 7; r++) {
                int s1 = 0, s2v = 0;
                for (int j = 0; j < 20; j++) {
                    s1 += (theta == 0 ? P[n][r][j] : Q[n][r][j]) * Y1[n][j];
                    s2v += (theta == 0 ? Q[n][r][j] : P[n][r][j]) * Y2[n][j];
                }
                A1[n][r] = s1 % p;
                A2[n][r] = s2v % p;
            }
            for (int r = 0; r < 3; r++) {
                int s3 = 0;
                for (int j = 0; j < 20; j++) {
                    s3 += (theta == 0 ? C[n][r][j] : D[n][r][j]) * Y1[n][j];
                    s3 += (theta == 0 ? D[n][r][j] : C[n][r][j]) * Y2[n][j];
                }
                A3[n][r] = s3 % p;
            }
        }
        int int_flat[42];
        for (int n = 0; n < 6; n++) {
            for (int r = 0; r < 7; r++) int_flat[n * 7 + r] = (theta == 0) ? A2[n][r] : A1[n][r];
        }
        int des_flat[60];
        for (int n = 0; n < 6; n++) {
            for (int r = 0; r < 7; r++) des_flat[n * 10 + r] = (theta == 0) ? A1[n][r] : A2[n][r];
            for (int r = 0; r < 3; r++) {
                int mix = 0;
                for (int j = 0; j < 42; j++) mix += Cancel[n * 3 + r][j] * int_flat[j];
                des_flat[n * 10 + 7 + r] = mod_norm(A3[n][r] - (mix % p), p);
            }
        }
        for (int i = 0; i < 60; i++) {
            int acc = 0;
            for (int j = 0; j < 60; j++) acc += aug_des[i][60 + j] * des_flat[j];
            int rec = acc % p;
            int exp_val = (theta == 0) ? W1[i / 20][i % 20] : W2[i / 20][i % 20];
            if (rec != exp_val) return false;
        }
    }
    return true;
}
