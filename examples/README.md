<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Examples (`examples/`)

Self-contained runnable demonstrations of the `coded-pir-mlwe-complexity-lab` computational verification engines.

## Quickstart Demo

```bash
PYTHONPATH=python python examples/quickstart_demo.py
```

Outputs a live, deterministic verification summary across all three pillars:
1. **Pillar I (`CS-053`):** Koszul–Veronese $(E,K,T)=(6,3,3)$ rate $10/17 > 4/7$ vs. Sun–Zhang LFSR, $\mathbb{F}_{11}$ Byzantine rate-$2/5$ rank audit, and `h_uncond` $8/13 > 3/5$ barrier check.
2. **Pillar II (`CS-026`):** 60-digit ML-KEM $\mathrm{CBD}_2$ vs. $\mathrm{CBD}_3$ Rényi-2 optimization (`4.96x` tightness cliff), Chen Step-9 anti-periodic DFT even-mode cancellation, and QGTL shifted-LWE Berry curvature.
3. **Pillar III (`CS-001` / `CS-051`):** Exact FIPS 203 `Compress_1` margin ($|e| \le 831$, sharp failure at $+832$) and additive MLWE-PIR depth ceiling.
