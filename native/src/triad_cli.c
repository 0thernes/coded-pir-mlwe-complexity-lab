/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander S. Donahue
 */
#include "triad_core.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: triad_cli <koszul|f11-byz|chen|qgtl|renyi|dyadic256|dyadic512|dyadic1024a|dyadic1024b|twisted|koszul-tensor|strassen|koszul-allm|lovasz-c5|c7-cap>\n");
        return 2;
    }
    if (strcmp(argv[1], "koszul") == 0) {
        int T = (argc > 2) ? atoi(argv[2]) : 3;
        int Tp = (argc > 3) ? atoi(argv[3]) : 2;
        int K = (argc > 4) ? atoi(argv[4]) : 3;
        int rk = triad_verify_koszul_rank(T, Tp, K, 101);
        printf("{\"T\":%d,\"Tp\":%d,\"K\":%d,\"rank\":%d}\n", T, Tp, K, rk);
        return 0;
    }
    if (strcmp(argv[1], "f11-byz") == 0) {
        bool ok = triad_verify_f11_byzantine_rate25();
        printf("{\"f11_byzantine_rate25\":%s}\n", ok ? "true" : "false");
        return ok ? 0 : 1;
    }
    if (strcmp(argv[1], "chen") == 0) {
        int D = (argc > 2) ? atoi(argv[2]) : 5;
        int c = (argc > 3) ? atoi(argv[3]) : 3;
        triad_chen_res_t r = triad_verify_chen_step9(D, c);
        printf("{\"D\":%d,\"c\":%d,\"max_even_mag\":%.3e,\"max_odd_mag\":%.6f,\"passed\":%s}\n",
               r.D, r.c, r.max_even_mag, r.max_odd_mag, r.passed ? "true" : "false");
        return r.passed ? 0 : 1;
    }
    if (strcmp(argv[1], "qgtl") == 0) {
        int eta = (argc > 2) ? atoi(argv[2]) : 2;
        double sigma = (argc > 3) ? atof(argv[3]) : 1.023;
        double e0 = (argc > 4) ? atof(argv[4]) : 0.25;
        triad_qgtl_res_t r = triad_qgtl_shifted_lwe(eta, sigma, e0);
        printf("{\"g_tt\":%.12f,\"g_ss\":%.12f,\"g_ts\":%.12f,\"omega_ts\":%.12f,\"cov_formula\":%.12f,\"max_err\":%.3e}\n",
               r.g_tt, r.g_ss, r.g_ts, r.omega_ts, r.cov_formula, r.max_err);
        return 0;
    }
    if (strcmp(argv[1], "renyi") == 0) {
        int eta = (argc > 2) ? atoi(argv[2]) : 2;
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
        int m = (argc > 2) ? atoi(argv[2]) : 4;
        int D = (argc > 3) ? atoi(argv[3]) : 5;
        int r = (argc > 4) ? atoi(argv[4]) : 1;
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
        int m = (argc > 2) ? atoi(argv[2]) : 3;
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
    fprintf(stderr, "Unknown command: %s\n", argv[1]);
    return 2;
}
