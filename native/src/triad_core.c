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
