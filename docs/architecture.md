<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# System & Mathematical Architecture (`docs/architecture.md`)

`coded-pir-mlwe-complexity-lab` (`v4.0.0`) is structured as a four-layer verification stack where every mathematical claim flows downward from 27 formal machine-checked Lean 4.35.0 proofs (`T1a`–`T3j`) into independent C11, Eshkol dual-number AD, and 60-digit exact Python checks, and upward into the AMS-LaTeX preprint and interactive GitHub Pages Proof Blueprint.

```text
                        +----------------------------------------------+
                        |  paper/main.tex (AMS-LaTeX Preprint v4.0.0)  |
                        |  + 7 Vector PDF Figures + refs.bib (33 HTTP) |
                        |  + docs/site/ Interactive Proof Blueprint    |
                        +----------------------+-----------------------+
                                               |
             +---------------------------------+---------------------------------+
             |                                 |                                 |
+------------v-------------+     +-------------v--------------+     +------------v-------------+
| Tier 1: Lean 4.35.0      |     | Tier 2: Multi-Language     |     | Tier 3: Governance &     |
| Zero-Mathlib TCB (27)    |     | Computational Cross-Audit  |     | Provenance Layer         |
|  - AlgebraCore.lean      |     |  - native/ (C11 65 tests)  |     |  - CLAIMS.md (C1-C27)    |
|  - PIRCertificates/Lin.  |     |  - eshkol/ (Dual-Num AD)   |     |  - LIMITATIONS.md        |
|  - PIRKoszul.lean (T1a-i)|     |  - python/triad_verify/    |     |  - HARDENING_LOG.md      |
|  - MLWETightness (T2a-h) |     |  - tests/test_all.py       |     |  - MANIFEST.sha256       |
|  - KoszulTensor (T3e,g)  |     |    (17 tests, 12/12 muts)  |     |  - rosette_receipt.json  |
|  - Strassen/Brockett(h,i)|     +----------------------------+     |  - SLSA CI Attestation   |
|  - ShannonCapacity (T3j) |                                        +--------------------------+
|  - ComplexityTriad(T3a-f)|
|  - NonVacuity & Palomar  |
+--------------------------+
```

## Pillar Dependency Architecture

1. **Pillar I (`CS-053` — Coded, Colluding, Robust & Byzantine PIR):**
   - `TriadFrontier/AlgebraCore.lean` defines zero-Mathlib `CommRing`, `SimpleField`, `rPow`, `chooseNat`, and `PairwiseNeq`.
   - `TriadFrontier/PIRCertificates.lean` stores $O(\log N)$ balanced binary-tree lookup certificates for the $\mathbb{F}_{11}$ rate-$2/5$ Byzantine witness (90 exact matrix inverses) and the 330-orbit pure-integer scale-128 polymatroid `h_uncond` (all 270,336 elemental Shannon inequalities + 99 PIR equalities + 1,485 singleton Ingletons).
   - `TriadFrontier/PIRLinearCerts.lean` certifies all 23 $\mathbb{F}_2/\mathbb{F}_3$ linear-subspace 4-variable rays, denominator-3 decompositions of all 24 canonical profiles covering ALL 510 four-marginals of `h_uncond`, and exact $\mathbb{F}_2$-linear subspace realizations of ALL 6 five-object retrieval marginals (`T1i`).
   - `TriadFrontier/PIRKoszul.lean` proves `T1a`–`T1i`.
2. **Pillar II (`CS-026`, `QC-042`, `CM-048` — Module-LWE Reduction Tightness, `Dyadic-256/512/1024-A/B`, & QGTL Geometry):**
   - `TriadFrontier/MLWETightness.lean` proves `T2a`–`T2h` (Luo determinant-ideal invariance, Chen Step-9 anti-periodic DFT cancellation, FIPS 203 $\mathrm{CBD}_2/\mathrm{CBD}_3$ $4.96\times$ cliff, QGTL shifted-LWE Berry curvature, Cauchy–Schwarz floor + 1-byte `Dyadic-256` + QGTL PSD, universal $m$-twisted DFT rule, Pearson $\chi^2$/Hermite-4 variational bridge + 9-bit `Dyadic-512`, and all-order Rényi-$(m+1)$ Hölder floor + TV–$\chi^2$ bridge + 10-bit Bai-optimal `Dyadic-1024-A/B`).
3. **Pillar III (`CS-001`, `CS-004`, `CS-010`, `CS-012`, `CS-051`, `CS-CMP-012`, Cross-Pillar Unification):**
   - `TriadFrontier/KoszulTensor.lean` proves `T3e` and `T3g` (field-universal Koszul flattening bounds $\mathrm{rank}_F(\langle 2,2,2\rangle) \ge 6$, $\mathrm{rank}_F(T_3) \ge 5$, and symbolic ALL-$m$ $\mathrm{rank}_F(\langle m,m,m\rangle) \ge m^2 + 2$ plus ceiling $m^2+m$).
   - `TriadFrontier/StrassenWinograd.lean` proves `T3h` (complete characteristic-free Exact Strassen–Winograd $\mathrm{rank}_F(\langle 2,2,2\rangle) = 7$ over every `SimpleField F`, including $\mathbb{F}_2$).
   - `TriadFrontier/BrockettDobkin.lean` proves `T3i` (field-universal rectangular Brockett–Dobkin bound, quadratic $\mathrm{rank}_F(\langle m,m,m\rangle) \ge 2m^2-m$ beating $m^2+m$ for all $m \ge 3$, and Strassen lift $\mathrm{rank}_F(\langle m,2,p\rangle) \ge mp+3$).
   - `TriadFrontier/ShannonCapacity.lean` proves `T3j` (field-universal Haemers bound $|S| \le r^t$, exact zero-reals $\mathbb{Z}[\sqrt{5}]$ SOS proof of Lovász $\Theta(C_5)=\sqrt{5}$, and exact $C_7$ minimum Haemers rank $= 4$ over every field $F$).
   - `TriadFrontier/ComplexityTriad.lean` proves `T3a`–`T3d` and `T3f` (Algebrization MLE uniqueness, LWE PRF $\to$ Natural Proofs, Katz–Trevisan Byzantine PIR $\leftrightarrow$ LDC distance & smoothness, FIPS 203 `Compress_1` margin $|e| \le 831$, and Shannon finite circuit counting).
4. **Palomar 6-Kernel Verification Boundary:**
   - `lean/Challenge.lean` defines all 27 theorem propositions (`T1a`–`T3j`) and their conjunction.
   - `lean/Solution.lean` exports the verified proofs; `lean/VerifyAxioms.lean` runs `#print axioms` on all 29 audited declarations (27 theorems + master conjunction + `nonvac_all_hypotheses`).
   - `lean/PalomarChallenge.lean` (excluded from `defaultTargets`) and `lean/PalomarSolution.lean` form the exact contract judged by `lake comparator --config comparator.json --paranoid` (3,589 `con-leche`/`con-ron` & 3,884 `nanoda` declarations).
