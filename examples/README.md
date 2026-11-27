<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Examples (`examples/`)

Self-contained runnable demonstrations of the `coded-pir-mlwe-complexity-lab` (`v5.1.0`) computational verification engines.

## Quickstart Demo

```bash
PYTHONPATH=python python examples/quickstart_demo.py
```

Outputs a live, deterministic verification summary across all three pillars:
1. **Pillar I (`CS-053`):** Numerical interference-rank 42 / rate $10/17$ for one $(E,K,T)=(6,3,3)$ design (privacy and zero-error decoding not verified), $\mathbb{F}_{11}$ Byzantine rate-$2/5$ rank audit, and the single $\mathbb{Z}_4$-cyclic $\mathbb{F}_2^{64}$ 6-subspace realization (`T1j`, 64/64 subsets matched at exact scale 4).
2. **Pillar II (`CS-026` / `QC-042` / `CM-048`):** 60-digit ML-KEM $\mathrm{CBD}_2$ vs. $\mathrm{CBD}_3$ Rényi-2 cliff (`4.96x`), branchless 8/9/10/14-bit `Dyadic-256`, `Dyadic-512` ($\kappa_{\mathrm{ex}}=0$), `Dyadic-1024-A/B`, and `Dyadic-16384-A/B` (ML-KEM-1024 Bai overhead $11.17\times$ to `6.013` b and ML-KEM-512 $41.9\times$ to `0.5916` b, with `float64` discrete-convolution model DFRs), anti-periodic / $m$-twisted DFT cancellation, and covariance/QGTL checks.
3. **Pillar III (`CS-001` / `CS-004` / `CS-012` / `CS-051` / `CS-CMP-012`):** Multilinear-extension uniqueness, $B$-error-correcting minimum distance, exact NIST FIPS 203 Eq. (4.7) `Compress_1` margins ($|e| \le 832$ for $b=0$; $-832 \le e \le 831$ for $b=1$; sharp failures at $+833$ and $+832$), Exact Strassen–Winograd $\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$ ($\forall F$), All-$m$ Koszul & $2m^2-m$ substitution bound, Multivariate Schwartz–Zippel & two-sided Strassen bound, integer Lovász $\Theta(C_5)=\sqrt{5}$ + $C_7$ min Haemers rank $4$, and the conditional Paley conference family $\Theta(P_p)=\sqrt{p}$ ($P_5..P_{41}$).
