<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Examples (`examples/`)

Self-contained runnable demonstrations of the `coded-pir-mlwe-complexity-lab` computational verification engines.

## Quickstart Demo

```bash
PYTHONPATH=python python examples/quickstart_demo.py
```

Outputs a live, deterministic verification summary across all three pillars:
1. **Pillar I (`CS-053`):** Koszul–Veronese $(E,K,T)=(6,3,3)$ rate $10/17 > 4/7$ vs. Sun–Zhang LFSR and $\mathbb{F}_{11}$ Byzantine rate-$2/5$ rank audit.
2. **Pillar II (`CS-026` / `CM-048`):** 60-digit ML-KEM $\mathrm{CBD}_2$ vs. $\mathrm{CBD}_3$ Rényi-2 cliff (`4.96x`), constant-time `Dyadic-256` (`17.7x` drop) and 9-bit zero-excess-kurtosis `Dyadic-512` (`12.9x` drop) with exact FIPS 203 DFRs (`512`/`768`/`1024`), Chen Step-9 anti-periodic DFT cancellation, and QGTL Berry curvature.
3. **Pillar III (`CS-001` / `CS-004` / `CS-012` / `CS-051`):** Algebrization MLE uniqueness, Katz–Trevisan LDC distance, FIPS 203 `Compress_1` margin ($|e| \le 831$, sharp failure at $+832$), Exact Strassen–Winograd $\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$ ($\forall F$), and symbolic All-$m$ Koszul MatMul bounds ($\ge m^2+2$).
