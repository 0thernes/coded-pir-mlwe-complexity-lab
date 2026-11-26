/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander S. Donahue
 *
 * libFuzzer + standalone fuzzing harness for TriadFrontier C11 verification core.
 */
#include "triad_core.h"

#include <math.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size < 4) {
        return 0;
    }

    /* 1. Fuzz finite-field modular inversion and matrix rank over F_11 / F_101 */
    const int p = (data[0] & 1U) ? 11 : 101;
    const int a = (int)(data[1] % (uint8_t)p);
    if (a != 0) {
        const int inv = triad_mod_inv(a, p);
        if ((a * inv) % p != 1) {
            abort();
        }
    }

    int mat[16];
    for (int i = 0; i < 16; ++i) {
        mat[i] = (int)(data[i % size] % (uint8_t)p);
    }
    const int r = triad_rank_mod_p(mat, 4, 4, p);
    if (r < 0 || r > 4) {
        abort();
    }

    /* 2. Fuzz FIPS 203 Compress_1 margin invariant */
    const uint16_t raw_u = (uint16_t)(((uint16_t)data[2] << 8) | (uint16_t)data[3]);
    const int e = (int)(raw_u % 1663U) - 831; /* strictly in [-831, +831] */
    if (e < -831 || e > 831) {
        abort();
    }
    if (triad_mlkem_compress1(e) != 0) {
        abort();
    }
    if (triad_mlkem_compress1(1665 + e) != 1) {
        abort();
    }

    /* 3. Fuzz QGTL Berry curvature numerical identity & parity */
    const int eta = (data[0] & 2U) ? 3 : 2;
    const double sigma = 0.6 + ((double)data[1] / 255.0) * 1.4;
    const double e0 = -1.5 + ((double)data[2] / 255.0) * 3.0;
    const triad_qgtl_res_t qres = triad_qgtl_shifted_lwe(eta, sigma, e0);
    if (!isfinite(qres.omega_ts) || !isfinite(qres.max_err) || qres.max_err > 1e-11) {
        abort();
    }

    /* 4. Fuzz Chen Step-9 odd D, odd c anti-periodic cancellation */
    const int D = 3 + 2 * (int)(data[3] % 7U);
    const int c = 1 + 2 * (int)(data[0] % 7U);
    const triad_chen_res_t cres = triad_verify_chen_step9(D, c);
    if (!cres.passed) {
        abort();
    }

    /* 5. Fuzz 10-bit constant-time Dyadic-1024-A and Dyadic-1024-B range bounds */
    const int va = triad_dyadic1024a_sample_ct(raw_u);
    const int vb = triad_dyadic1024b_sample_ct(raw_u);
    if (va < -3 || va > 3 || vb < -4 || vb > 4) {
        abort();
    }

    return 0;
}

#ifdef FUZZ_STANDALONE
int main(void) {
    uint8_t buf[32];
    uint32_t state = 0x13579BDFu;
    for (int iter = 0; iter < 512; ++iter) {
        for (size_t i = 0; i < sizeof(buf); ++i) {
            state = state * 1664525u + 1013904223u;
            buf[i] = (uint8_t)(state >> 24);
        }
        LLVMFuzzerTestOneInput(buf, sizeof(buf));
    }
    printf("fuzz_triad standalone smoke: 512/512 iterations PASSED\n");
    return 0;
}
#endif
