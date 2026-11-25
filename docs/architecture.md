<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# System & Mathematical Architecture (`docs/architecture.md`)

`coded-pir-mlwe-complexity-lab` is structured as a four-layer verification stack where every mathematical claim flows downward from formal machine-checked Lean 4.35.0 proofs into independent C11, Eshkol dual-number AD, and 60-digit exact Python checks, and upward into the 11-page AMS-LaTeX preprint.

```text
                        +----------------------------------------------+
                        |  paper/main.tex (11-page AMS-LaTeX Preprint) |
                        |  + 4 Vector PDF Figures + refs.bib (23 HTTP) |
                        +----------------------+-----------------------+
                                               |
             +---------------------------------+---------------------------------+
             |                                 |                                 |
+------------v-------------+     +-------------v--------------+     +------------v-------------+
| Tier 1: Lean 4.35.0      |     | Tier 2: Multi-Language     |     | Tier 3: Governance &     |
| Zero-Mathlib TCB         |     | Computational Cross-Audit  |     | Provenance Layer         |
|  - AlgebraCore.lean      |     |  - native/ (C11 -Werror)   |     |  - CLAIMS.md             |
|  - PIRCertificates.lean  |     |  - eshkol/ (Dual-Num AD)   |     |  - LIMITATIONS.md        |
|  - PIRKoszul.lean (T1a-f)|     |  - python/triad_verify/    |     |  - HARDENING_LOG.md      |
|  - MLWETightness (T2a-d) |     |  - tests/test_all.py       |     |  - MANIFEST.sha256       |
|  - ComplexityTriad(T3a-d)|     |    (diff/prop/neg/mutants) |     |  - rosette_receipt.json  |
|  - NonVacuity.lean       |     +----------------------------+     |  - SLSA CI Attestation   |
|  - Palomar Comparator    |                                        +--------------------------+
+--------------------------+
```

## Pillar Dependency Architecture

1. **Pillar I (`CS-053` — Coded, Colluding, Robust & Byzantine PIR):**
   - `TriadFrontier/AlgebraCore.lean` defines zero-Mathlib `CommRing`, `SimpleField`, `rPow`, `chooseNat`, and `PairwiseNeq`.
   - `TriadFrontier/PIRCertificates.lean` stores $O(\log N)$ balanced binary-tree lookup certificates for the $\mathbb{F}_{11}$ rate-$2/5$ Byzantine witness (90 exact matrix inverses) and the 330-orbit pure-integer scale-128 polymatroid `h_uncond` (all 270,336 elemental Shannon inequalities + 99 PIR equalities + 1,485 singleton Ingletons).
   - `TriadFrontier/PIRKoszul.lean` proves `T1a`–`T1f`.
2. **Pillar II (`CS-026` — Module-LWE Reduction Tightness & Cryptanalytic Obstructions):**
   - `TriadFrontier/MLWETightness.lean` proves `T2a`–`T2d` (Luo determinant-ideal invariance, Chen Step-9 anti-periodic DFT cancellation, FIPS 203 $\mathrm{CBD}_2/\mathrm{CBD}_3$ exact moments & $4.96\times$ Rényi-2 cliff, and QGTL shifted-LWE Berry curvature).
3. **Pillar III (`CS-001`, `CS-051`, Cross-Pillar Unification):**
   - `TriadFrontier/ComplexityTriad.lean` proves `T3a`–`T3d`, linking Algebrization multilinear uniqueness (`CS-001`), LWE PRFs $\to$ Natural Proofs (`CS-026 → CS-001`), Katz–Trevisan Byzantine PIR $\leftrightarrow$ LDC minimum Hamming distance $2B+1$ (`CS-053 ↔ CS-051`), and FIPS 203 `Compress_1` single-server MLWE-PIR noise ceiling (`CS-026 ↔ CS-053`).
4. **Palomar 6-Kernel Verification Boundary:**
   - `lean/Challenge.lean` defines the 14 theorem propositions (`T1a`–`T3d`) and their conjunction.
   - `lean/Solution.lean` exports the verified proofs; `lean/VerifyAxioms.lean` runs `#print axioms` on all 16 audited declarations (14 theorems + master conjunction + `nonvac_all_hypotheses`).
   - `lean/PalomarChallenge.lean` (excluded from `defaultTargets`) and `lean/PalomarSolution.lean` form the exact contract judged by `lake comparator --config comparator.json --paranoid`.
