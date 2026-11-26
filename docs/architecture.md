<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# System & Mathematical Architecture (`docs/architecture.md`)

`coded-pir-mlwe-complexity-lab` (`v3.0.0`) is structured as a four-layer verification stack where every mathematical claim flows downward from 23 formal machine-checked Lean 4.35.0 proofs (`T1a`–`T3h`) into independent C11, Eshkol dual-number AD, and 60-digit exact Python checks, and upward into the 16-page AMS-LaTeX preprint and interactive GitHub Pages Proof Blueprint.

```text
                        +----------------------------------------------+
                        |  paper/main.tex (16-page AMS-LaTeX Preprint) |
                        |  + 6 Vector PDF Figures + refs.bib (28 HTTP) |
                        |  + docs/site/ Interactive Proof Blueprint    |
                        +----------------------+-----------------------+
                                               |
             +---------------------------------+---------------------------------+
             |                                 |                                 |
+------------v-------------+     +-------------v--------------+     +------------v-------------+
| Tier 1: Lean 4.35.0      |     | Tier 2: Multi-Language     |     | Tier 3: Governance &     |
| Zero-Mathlib TCB (23)    |     | Computational Cross-Audit  |     | Provenance Layer         |
|  - AlgebraCore.lean      |     |  - native/ (C11 57 tests)  |     |  - CLAIMS.md (C1-C23)    |
|  - PIRCertificates.lean  |     |  - eshkol/ (Dual-Num AD)   |     |  - LIMITATIONS.md        |
|  - PIRKoszul.lean (T1a-h)|     |  - python/triad_verify/    |     |  - HARDENING_LOG.md      |
|  - MLWETightness (T2a-g) |     |  - tests/test_all.py       |     |  - MANIFEST.sha256       |
|  - KoszulTensor (T3e,g)  |     |    (16 tests, 10/10 muts)  |     |  - rosette_receipt.json  |
|  - StrassenWinograd(T3h) |     +----------------------------+     |  - SLSA CI Attestation   |
|  - ComplexityTriad(T3a-f)|                                        +--------------------------+
|  - NonVacuity & Palomar  |
+--------------------------+
```

## Pillar Dependency Architecture

1. **Pillar I (`CS-053` — Coded, Colluding, Robust & Byzantine PIR):**
   - `TriadFrontier/AlgebraCore.lean` defines zero-Mathlib `CommRing`, `SimpleField`, `rPow`, `chooseNat`, and `PairwiseNeq`.
   - `TriadFrontier/PIRCertificates.lean` stores $O(\log N)$ balanced binary-tree lookup certificates for the $\mathbb{F}_{11}$ rate-$2/5$ Byzantine witness (90 exact matrix inverses) and the 330-orbit pure-integer scale-128 polymatroid `h_uncond` (all 270,336 elemental Shannon inequalities + 99 PIR equalities + 1,485 singleton Ingletons).
   - `TriadFrontier/PIRKoszul.lean` proves `T1a`–`T1h` (including exact Zhang–Yeung 1998 and infinite Matúš 2007 $M_s$ cone reductions, symmetric $M \ge 3$ 1-flag Koszul, and exact all-$M$ contraction $\rho_{\mathrm{KV}}^j < \rho_{\mathrm{LFSR}}^j$).
2. **Pillar II (`CS-026`, `QC-042`, `CM-048` — Module-LWE Reduction Tightness, `Dyadic-256`/`Dyadic-512`, & QGTL Geometry):**
   - `TriadFrontier/MLWETightness.lean` proves `T2a`–`T2g` (Luo determinant-ideal invariance, Chen Step-9 anti-periodic DFT cancellation, FIPS 203 $\mathrm{CBD}_2/\mathrm{CBD}_3$ $4.96\times$ cliff, QGTL shifted-LWE Berry curvature, Cauchy–Schwarz finite-support floor + 1-byte `Dyadic-256` $17.7\times$ collapse + QGTL Provost–Vallée PSD & Metric–Kurtosis ordering, universal $m$-twisted DFT selection rule, Pearson $\chi^2$/Hermite-4 variational Rényi-2 bridge, and 9-bit zero-excess-kurtosis `Dyadic-512` $12.9\times$ collapse matching exact Gaussian $\det(g)=1/2$).
3. **Pillar III (`CS-001`, `CS-004`, `CS-010`, `CS-012`, `CS-051`, Cross-Pillar Unification):**
   - `TriadFrontier/KoszulTensor.lean` proves `T3e` and `T3g` (universal Steinitz/Gauss rank bound + Landsberg–Ottaviani Koszul flattenings certifying $\mathrm{rank}_F(\langle 2,2,2\rangle) \ge 6$, $\mathrm{rank}_F(T_3) \ge 5$, and symbolic ALL-$m$ $\mathrm{rank}_F(\langle m,m,m\rangle) \ge m^2 + 2$ plus ceiling $m^2+m$ over every field $F$ including characteristic 2).
   - `TriadFrontier/StrassenWinograd.lean` proves `T3h` (complete characteristic-free Exact Strassen–Winograd $\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$ over every `SimpleField F`, including $\mathbb{F}_2$).
   - `TriadFrontier/ComplexityTriad.lean` proves `T3a`–`T3d` and `T3f` (Algebrization MLE uniqueness, LWE PRF $\to$ Natural Proofs, Katz–Trevisan Byzantine PIR $\leftrightarrow$ LDC distance & smoothness, FIPS 203 `Compress_1` margin $|e| \le 831$, and Shannon finite circuit counting).
4. **Palomar 6-Kernel Verification Boundary:**
   - `lean/Challenge.lean` defines all 23 theorem propositions (`T1a`–`T3h`) and their conjunction.
   - `lean/Solution.lean` exports the verified proofs; `lean/VerifyAxioms.lean` runs `#print axioms` on all 25 audited declarations (23 theorems + master conjunction + `nonvac_all_hypotheses`).
   - `lean/PalomarChallenge.lean` (excluded from `defaultTargets`) and `lean/PalomarSolution.lean` form the exact contract judged by `lake comparator --config comparator.json --paranoid` (2,995 `con-leche`/`con-ron` declarations).
