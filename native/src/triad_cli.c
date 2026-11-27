/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander S. Donahue
 */
#include "triad_core.h"

#include <errno.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static bool parse_int_range(const char *s, int lo, int hi, int *out) {
    if (!s || *s == '\0') return false;
    errno = 0;
    char *end = NULL;
    long v = strtol(s, &end, 10);
    if (errno != 0 || end == s || *end != '\0' || v < (long)lo || v > (long)hi) {
        return false;
    }
    *out = (int)v;
    return true;
}

static bool parse_double_range(const char *s, double lo, double hi, double *out) {
    if (!s || *s == '\0') return false;
    errno = 0;
    char *end = NULL;
    double v = strtod(s, &end);
    if (errno != 0 || end == s || *end != '\0' || !isfinite(v) || v < lo || v > hi) {
        return false;
    }
    *out = v;
    return true;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: triad_cli <koszul|f11-byz|ret6-f2|chen|qgtl|renyi|dyadic256|dyadic512|dyadic1024a|dyadic1024b|dyadic16384a|dyadic16384b|twisted|koszul-tensor|strassen|koszul-allm|lovasz-c5|c7-cap|paley-cap>\n");
        return 2;
    }
    if (strcmp(argv[1], "koszul") == 0) {
        int T = 3, Tp = 2, K = 3;
        if (argc > 2 && !parse_int_range(argv[2], 1, 6, &T)) {
            fprintf(stderr, "Invalid T (expected integer in 1..6): %s\n", argv[2]);
            return 2;
        }
        if (argc > 3 && !parse_int_range(argv[3], 1, T, &Tp)) {
            fprintf(stderr, "Invalid Tp (expected integer in 1..%d): %s\n", T, argv[3]);
            return 2;
        }
        if (argc > 4 && !parse_int_range(argv[4], 1, 8, &K)) {
            fprintf(stderr, "Invalid K (expected integer in 1..8): %s\n", argv[4]);
            return 2;
        }
        int rk = triad_verify_koszul_rank(T, Tp, K, 101);
        if (rk < 0) {
            fprintf(stderr, "Koszul rank computation failed for (T=%d, Tp=%d, K=%d)\n", T, Tp, K);
            return 1;
        }
        printf("{\"T\":%d,\"Tp\":%d,\"K\":%d,\"rank\":%d}\n", T, Tp, K, rk);
        return 0;
    }
    if (strcmp(argv[1], "f11-byz") == 0) {
        bool ok = triad_verify_f11_byzantine_rate25();
        printf("{\"f11_byzantine_rate25\":%s}\n", ok ? "true" : "false");
        return ok ? 0 : 1;
    }
    if (strcmp(argv[1], "chen") == 0) {
        int D = 5, c = 3;
        if (argc > 2 && !parse_int_range(argv[2], 1, 2048, &D)) {
            fprintf(stderr, "Invalid D (expected integer in 1..2048): %s\n", argv[2]);
            return 2;
        }
        if (argc > 3 && !parse_int_range(argv[3], -100000, 100000, &c)) {
            fprintf(stderr, "Invalid c (expected integer in -100000..100000): %s\n", argv[3]);
            return 2;
        }
        triad_chen_res_t r = triad_verify_chen_step9(D, c);
        printf("{\"D\":%d,\"c\":%d,\"max_even_mag\":%.3e,\"max_odd_mag\":%.6f,\"passed\":%s}\n",
               r.D, r.c, r.max_even_mag, r.max_odd_mag, r.passed ? "true" : "false");
        return r.passed ? 0 : 1;
    }
    if (strcmp(argv[1], "qgtl") == 0) {
        int eta = 2;
        double sigma = 1.023;
        double e0 = 0.25;
        if (argc > 2 && !parse_int_range(argv[2], 1, 7, &eta)) {
            fprintf(stderr, "Invalid eta (expected integer in 1..7): %s\n", argv[2]);
            return 2;
        }
        if (argc > 3 && !parse_double_range(argv[3], 1e-3, 100.0, &sigma)) {
            fprintf(stderr, "Invalid sigma (expected finite number in [1e-3, 100]): %s\n", argv[3]);
            return 2;
        }
        if (argc > 4 && !parse_double_range(argv[4], -100.0, 100.0, &e0)) {
            fprintf(stderr, "Invalid e0 (expected finite number in [-100, 100]): %s\n", argv[4]);
            return 2;
        }
        triad_qgtl_res_t r = triad_qgtl_shifted_lwe(eta, sigma, e0);
        if (!isfinite(r.max_err)) {
            fprintf(stderr, "QGTL computation rejected invalid domain\n");
            return 1;
        }
        printf("{\"g_tt\":%.12f,\"g_ss\":%.12f,\"g_ts\":%.12f,\"omega_ts\":%.12f,\"cov_formula\":%.12f,\"max_err\":%.3e}\n",
               r.g_tt, r.g_ss, r.g_ts, r.omega_ts, r.cov_formula, r.max_err);
        return 0;
    }
    if (strcmp(argv[1], "renyi") == 0) {
        int eta = 2;
        if (argc > 2 && !parse_int_range(argv[2], 1, 7, &eta)) {
            fprintf(stderr, "Invalid eta (expected integer in 1..7): %s\n", argv[2]);
            return 2;
        }
        triad_renyi_res_t r = triad_mlkem_renyi_opt(eta);
        printf("{\"eta\":%d,\"sigma_opt_r2\":%.6f,\"min_r2\":%.12f,\"sigma_opt_rinf\":%.6f,\"min_rinf\":%.12f,\"bits_per_coord_r2\":%.12f}\n",
               r.eta, r.sigma_opt_r2, r.min_r2, r.sigma_opt_rinf, r.min_rinf, r.bits_per_coord_r2);
        return 0;
    }
    if (strcmp(argv[1], "dyadic256") == 0) {
        triad_renyi_res_t r = triad_mlkem_dyadic256_opt();
        printf("{\"dist\":\"dyadic256\",\"sigma_opt_r2\":%.6f,\"min_r2\":%.12f,\"min_rinf\":%.12f,\"bits_per_coord_r2\":%.12f,\"loss_1024_bits\":%.6f}\n",
               r.sigma_opt_r2, r.min_r2, r.min_rinf, r.bits_per_coord_r2, 2048.0 * r.bits_per_coord_r2);
        return 0;
    }
    if (strcmp(argv[1], "dyadic512") == 0) {
        triad_renyi_res_t r = triad_mlkem_dyadic512_opt();
        printf("{\"dist\":\"dyadic512\",\"sigma_opt_r2\":%.6f,\"min_r2\":%.12f,\"min_rinf\":%.12f,\"bits_per_coord_r2\":%.12f,\"loss_512_bits\":%.6f}\n",
               r.sigma_opt_r2, r.min_r2, r.min_rinf, r.bits_per_coord_r2, 1024.0 * r.bits_per_coord_r2);
        return 0;
    }
    if (strcmp(argv[1], "dyadic1024a") == 0) {
        triad_renyi_res_t r = triad_mlkem_dyadic1024a_opt();
        printf("{\"dist\":\"dyadic1024a\",\"sigma_opt_r2\":%.6f,\"min_r2\":%.12f,\"sigma_opt_rinf\":%.6f,\"min_rinf\":%.12f,\"bits_per_coord_r2\":%.12f,\"loss_1024_bits\":%.6f}\n",
               r.sigma_opt_r2, r.min_r2, r.sigma_opt_rinf, r.min_rinf, r.bits_per_coord_r2, 2048.0 * r.bits_per_coord_r2);
        return 0;
    }
    if (strcmp(argv[1], "dyadic1024b") == 0) {
        triad_renyi_res_t r = triad_mlkem_dyadic1024b_opt();
        printf("{\"dist\":\"dyadic1024b\",\"sigma_opt_r2\":%.6f,\"min_r2\":%.12f,\"sigma_opt_rinf\":%.6f,\"min_rinf\":%.12f,\"bits_per_coord_r2\":%.12f,\"loss_512_bits\":%.6f}\n",
               r.sigma_opt_r2, r.min_r2, r.sigma_opt_rinf, r.min_rinf, r.bits_per_coord_r2, 1024.0 * r.bits_per_coord_r2);
        return 0;
    }
    if (strcmp(argv[1], "twisted") == 0) {
        int m = 4, D = 5, r = 1;
        if (argc > 2 && !parse_int_range(argv[2], 2, 64, &m)) {
            fprintf(stderr, "Invalid m (expected integer in 2..64): %s\n", argv[2]);
            return 2;
        }
        if (argc > 3 && !parse_int_range(argv[3], 1, 256, &D)) {
            fprintf(stderr, "Invalid D (expected integer in 1..256): %s\n", argv[3]);
            return 2;
        }
        if (argc > 4 && !parse_int_range(argv[4], 0, m - 1, &r)) {
            fprintf(stderr, "Invalid r (expected integer in 0..%d): %s\n", m - 1, argv[4]);
            return 2;
        }
        double mf = 0.0;
        bool ok = triad_verify_twisted_dft(m, D, r, &mf);
        printf("{\"m\":%d,\"D\":%d,\"r\":%d,\"max_forbidden_mag\":%.3e,\"passed\":%s}\n",
               m, D, r, mf, ok ? "true" : "false");
        return ok ? 0 : 1;
    }
    if (strcmp(argv[1], "koszul-tensor") == 0) {
        bool ok = triad_verify_koszul_flattening_certs();
        printf("{\"koszul_flattening_m2_ge6_t3_ge5\":%s}\n", ok ? "true" : "false");
        return ok ? 0 : 1;
    }
    if (strcmp(argv[1], "strassen") == 0) {
        bool ok = triad_verify_strassen_7prod();
        printf("{\"strassen_7prod_exact\":%s,\"rank_M2_every_field\":7}\n", ok ? "true" : "false");
        return ok ? 0 : 1;
    }
    if (strcmp(argv[1], "koszul-allm") == 0) {
        int m = 3;
        if (argc > 2 && !parse_int_range(argv[2], 2, 5, &m)) {
            fprintf(stderr, "Invalid m (expected integer in 2..5): %s\n", argv[2]);
            return 2;
        }
        bool ok = triad_verify_all_m_koszul_monomial(m);
        printf("{\"m\":%d,\"monomial_left_inv_ok\":%s,\"rank_lb_every_field\":%d}\n",
               m, ok ? "true" : "false", m * m + 2);
        return ok ? 0 : 1;
    }
    if (strcmp(argv[1], "lovasz-c5") == 0) {
        bool ok = triad_verify_lovasz_c5_sos();
        printf("{\"lovasz_c5_zsqrt5_sos_exact\":%s,\"theta_c5_sq\":5}\n", ok ? "true" : "false");
        return ok ? 0 : 1;
    }
    if (strcmp(argv[1], "c7-cap") == 0) {
        bool ok = triad_verify_c7_indep10_and_haemers();
        printf("{\"c7_indep10_and_haemers_rank4_exact\":%s,\"min_haemers_rank_every_field\":4}\n", ok ? "true" : "false");
        return ok ? 0 : 1;
    }
    if (strcmp(argv[1], "dyadic16384a") == 0) {
        triad_renyi_res_t r = triad_mlkem_dyadic16384a_opt();
        printf("{\"dist\":\"dyadic16384a\",\"sigma_opt_r2\":%.6f,\"min_r2\":%.12f,\"sigma_opt_rinf\":%.6f,\"min_rinf\":%.12f,\"bits_per_coord_r2\":%.12f,\"loss_1024_bits\":%.6f}\n",
               r.sigma_opt_r2, r.min_r2, r.sigma_opt_rinf, r.min_rinf, r.bits_per_coord_r2, 2048.0 * r.bits_per_coord_r2);
        return 0;
    }
    if (strcmp(argv[1], "dyadic16384b") == 0) {
        triad_renyi_res_t r = triad_mlkem_dyadic16384b_opt();
        printf("{\"dist\":\"dyadic16384b\",\"sigma_opt_r2\":%.6f,\"min_r2\":%.12f,\"sigma_opt_rinf\":%.6f,\"min_rinf\":%.12f,\"bits_per_coord_r2\":%.12f,\"loss_512_bits\":%.6f}\n",
               r.sigma_opt_r2, r.min_r2, r.sigma_opt_rinf, r.min_rinf, r.bits_per_coord_r2, 1024.0 * r.bits_per_coord_r2);
        return 0;
    }
    if (strcmp(argv[1], "ret6-f2") == 0) {
        bool ok = triad_verify_ret6_f2_64();
        printf("{\"ret6_f2_64_all64_subsets_exact\":%s,\"scale_factor\":4}\n", ok ? "true" : "false");
        return ok ? 0 : 1;
    }
    if (strcmp(argv[1], "paley-cap") == 0) {
        int p = 13;
        if (argc > 2 && !parse_int_range(argv[2], 5, 41, &p)) {
            fprintf(stderr, "Invalid p (expected prime 1 mod 4 in 5..41): %s\n", argv[2]);
            return 2;
        }
        bool ok = triad_verify_paley_conference_sos(p);
        printf("{\"p\":%d,\"paley_zsqrtp_sos_and_selfcomp_exact\":%s,\"theta_sq\":%d}\n", p, ok ? "true" : "false", p);
        return ok ? 0 : 1;
    }
    fprintf(stderr, "Unknown command: %s\n", argv[1]);
    return 2;
}
