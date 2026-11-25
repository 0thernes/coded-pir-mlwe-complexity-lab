<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# System & Mathematical Architecture (`docs/architecture.md`)

`coded-pir-mlwe-complexity-lab` (`v2.0.0`) is structured as a four-layer verification stack where every mathematical claim flows downward from 19 formal machine-checked Lean 4.35.0 proofs (`T1a`–`T3f`) into independent C11, Eshkol dual-number AD, and 60-digit exact Python checks, and upward into the 14-page AMS-LaTeX preprint and interactive GitHub Pages Proof Blueprint.

```text
                        +----------------------------------------------+
                        |  paper/main.tex (14-page AMS-LaTeX Preprint) |
                        |  + 5 Vector PDF Figures + refs.bib (26 HTTP) |
                        |  + docs/site/ Interactive Proof Blueprint    |
                        +----------------------+-----------------------+
                                               |
             +---------------------------------+---------------------------------+
             |                                 |                                 |
+------------v-------------+     +-------------v--------------+     +------------v-------------+
| Tier 1: Lean 4.35.0      |     | Tier 2: Multi-Language     |     | Tier 3: Governance &     |
| Zero-Mathlib TCB (19)    |     | Computational Cross-Audit  |     | Provenance Layer         |
|  - AlgebraCore.lean      |     |  - native/ (C11 49 tests)  |     |  - CLAIMS.md (C1-C19)    |
|  - PIRCertificates.lean  |     |  - eshkol/ (Dual-Num AD)   |     |  - LIMITATIONS.md        |
|  - PIRKoszul.lean (T1a-g)|     |  - python/triad_verify/    |     |  - HARDENING_LOG.md      |
|  - MLWETightness (T2a-f) |     |  - tests/test_all.py       |     |  - MANIFEST.sha256       |
|  - KoszulTensor  (T3e)   |     |    (15 tests, 8/8 mutants) |     |  - rosette_receipt.json  |
|  - ComplexityTriad(T3a-f)|     +----------------------------+     |  - SLSA CI Attestation   |
|  - NonVacuity & Palomar  |                                        +--------------------------+
+--------------------------+
```

## Pillar Dependency Architecture

1. **Pillar I (`CS-053` — Coded, Colluding, Robust & Byzantine PIR):**
   - `TriadFrontier/AlgebraCore.lean` defines zero-Mathlib `CommRing`, `SimpleField`, `rPow`, `chooseNat`, and `PairwiseNeq`.
   - `TriadFrontier/PIRCertificates.lean` stores $O(\log N)$ balanced binary-tree lookup certificates for the $\mathbb{F}_{11}$ rate-$2/5$ Byzantine witness (90 exact matrix inverses) and the 330-orbit pure-integer scale-128 polymatroid `h_uncond` (all 270,336 elemental Shannon inequalities + 99 PIR equalities + 1,485 singleton Ingletons).
   - `TriadFrontier/PIRKoszul.lean` proves `T1a`–`T1g` (including exact Zhang–Yeung 1998 algebraic reduction and symmetric $M \ge 3$ 1-flag Koszul).
2. **Pillar II (`CS-026`, `QC-042`, `CM-048` — Module-LWE Reduction Tightness, `Dyadic-256`, & QGTL Geometry):**
   - `TriadFrontier/MLWETightness.lean` proves `T2a`–`T2f` (Luo determinant-ideal invariance, Chen Step-9 anti-periodic DFT cancellation, FIPS 203 $\mathrm{CBD}_2/\mathrm{CBD}_3$ $4.96\times$ cliff, QGTL shifted-LWE Berry curvature, Cauchy–Schwarz finite-support floor + 1-byte `Dyadic-256` $17.7\times$ collapse + QGTL Provost–Vallée PSD & Metric–Kurtosis ordering $3/8 < 15/32 < 1/2$, and universal $m$-twisted DFT selection rule).
3. **Pillar III (`CS-001`, `CS-004`, `CS-010`, `CS-012`, `CS-051`, Cross-Pillar Unification):**
   - `TriadFrontier/KoszulTensor.lean` proves `T3e` (universal Steinitz/Gauss rank bound + Landsberg–Ottaviani Koszul flattenings certifying $\mathrm{rank}_F(\langle 2,2,2\rangle) \ge 6$ and $\mathrm{rank}_F(T_3) \ge 5$ over every field $F$ including characteristic 2).
   - `TriadFrontier/ComplexityTriad.lean` proves `T3a`–`T3d` and `T3f` (Algebrization MLE uniqueness, LWE PRF $\to$ Natural Proofs, Katz–Trevisan Byzantine PIR $\leftrightarrow$ LDC distance & smoothness, FIPS 203 `Compress_1` margin $|e| \le 831$, and Shannon finite circuit counting).
4. **Palomar 6-Kernel Verification Boundary:**
   - `lean/Challenge.lean` defines all 19 theorem propositions (`T1a`–`T3f`) and their conjunction.
   - `lean/Solution.lean` exports the verified proofs; `lean/VerifyAxioms.lean` runs `#print axioms` on all 21 audited declarations (19 theorems + master conjunction + `nonvac_all_hypotheses`).
   - `lean/PalomarChallenge.lean` (excluded from `defaultTargets`) and `lean/PalomarSolution.lean` form the exact contract judged by `lake comparator --config comparator.json --paranoid` (2,418 `con-leche`/`con-ron` declarations).
