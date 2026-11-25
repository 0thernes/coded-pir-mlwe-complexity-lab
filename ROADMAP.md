<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Research Roadmap

## Completed in `v1.0.0`
- Machine-checked all 14 theorems (`T1a`–`T3d`) in zero-Mathlib Lean 4.35.0 across 6 independent kernels.
- Settled exact Koszul–Veronese Schur-product rank (`T1a`), exact linear $U$-$B$-MDS-$T$PIR capacity for $(2,N,2,2,U,B)$ (`T1c`), exact unrestricted capacity at $E=K+1$ (`T1c`–`T1d`), zero-error $T=3$ schemes (`10/17` and Byzantine `15/34`), and the pure-integer unconditioned Shannon+Ingleton barrier `h_uncond` (`T1e`) + projective $\mathbb{P}^3$ impossibility (`T1f`).
- Formally certified MLWE determinant-ideal secret independence (`T2a`), Chen Step-9 DFT cancellation (`T2b`), FIPS 203 4.96× Rényi-2 cliff (`T2c`), QGTL Berry curvature witness (`T2d`), and Algebrization + Triad bridges (`T3a`–`T3d`).

## Open Future Frontiers (Tier-4)
1. **Non-linear $C(2,4,2,2) \in [3/5, 8/13]$:** Determine whether 5+-variable non-Shannon inequalities close the gap to $3/5$, or whether an asymmetric non-linear scheme exceeds $3/5$.
2. **General $T \ge 4$ deterministic zero-error flag-private constructions:** Classify stabilizer orbits on $T$-tuples of flags $(P_n \subset Q_n)$ for $T \ge 4$.
3. **General $M \ge 3$ non-full-support-rank $U$-$B$-MDS-$T$PIR capacity:** Extend Koszul–Veronese squeezing beyond $M=2$ and $P$-out-of-$M$ multi-file retrieval.
4. **Tighter MLWE discrete-Gaussian-to-$\mathrm{CBD}_\eta$ reductions:** Investigate whether Rényi divergence of order $\alpha \in (1, 2)$ or smooth-Rényi arguments can narrow the 37.84-bit ML-KEM-1024 reduction cliff without altering FIPS 203 parameters.
