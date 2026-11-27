<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Examples (`examples/`)

Self-contained runnable demonstrations of the `coded-pir-mlwe-complexity-lab` (`v5.4.0`) computational verification engines.

## Quickstart Demo

```bash
PYTHONPATH=python python examples/quickstart_demo.py
```

Outputs a live, deterministic verification summary across all three pillars:
1. **Pillar I (`CS-053`):** Certified explicit $\mathbb{F}_{101}$ zero-error $T=3$-private $(N=6, K=3, T=3)$ rate-$10/17$ PIR witness (`data/f101_t3_k3_e6_witness.json`: `M_des = 60/60`, `M_pure = 42/42`, 20/20 invertible $\mathrm{GL}_{20}$ flag isomorphisms, 10/10 live zero-error encode/decode trials for $\theta \in \{0,1\}$, and 20/20 exact bit-for-bit colluder-transcript bijections $\Psi_I$, certified unconditionally inside the Lean 4.35.0 kernel by `T1k` + `T1l`), $\mathbb{F}_{11}$ Byzantine rate-$2/5$ rank audit, and the single $\mathbb{Z}_4$-cyclic $\mathbb{F}_2^{64}$ 6-subspace realization (`T1j`/`T1k`, 64/64 subsets proven equal to true vector-space `HasSpanDim` at scale 4).
2. **Pillar II (`CS-026` / `QC-042` / `CM-048`):** 60-digit ML-KEM $\mathrm{CBD}_2$ vs. $\mathrm{CBD}_3$ Rényi-2 cliff (`4.96x`), branchless 8/9/10/14-bit `Dyadic-256`, `Dyadic-512` ($\kappa_{\mathrm{ex}}=0$), `Dyadic-1024-A/B`, and `Dyadic-16384-A/B` (ML-KEM-1024 Bai overhead $11.17\times$ to `6.013` b and ML-KEM-512 $41.9\times$ to `0.5916` b), exact coupled FIPS 203 DFRs (`e^T r - s^T(e_1 + c_u) + e_2 + c_v`, cross-verified by a 90-digit Kronecker interval oracle reproducing NIST FIPS 203 Table 1 `-138.8`/`-164.8`/`-174.8` within `0.04` bits, showing the coupled Kurtosis–DFR–Rényi tradeoff and $1\%$ shrinkage $\sigma=0.990 \implies 2^{-177.25}$), anti-periodic / $m$-twisted DFT cancellation, and covariance/QGTL checks.
3. **Pillar III (`CS-001` / `CS-004` / `CS-012` / `CS-051` / `CS-CMP-012`):** Multilinear-extension uniqueness, $B$-error-correcting minimum distance, exact NIST FIPS 203 Eq. (4.7) `Compress_1` margins ($|e| \le 832$ for $b=0$; $-832 \le e \le 831$ for $b=1$; sharp failures at $+833$ and $+832$), Exact Strassen–Winograd $\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$ ($\forall F$), All-$m$ Koszul & $2m^2-m$ substitution bound, **Bläser's (FOCS 1999) $\frac{5}{2}m^2-3m$ lower bound (`T3m`, Bareiss exact $\det([X_m,Y_m])=1$ over $\mathbb{Z}$ and $\mathbb{F}_2$ for $m=2..12$, surpassing $2m^2-1$ for all $m \ge 6$)**, Multivariate Schwartz–Zippel & tightened Strassen–Bläser sandwich, integer Lovász $\Theta(C_5)=\sqrt{5}$ + $C_7$ min Haemers rank $4$, and the conditional Paley conference family $\Theta(P_p)=\sqrt{p}$ ($P_5..P_{41}$).
