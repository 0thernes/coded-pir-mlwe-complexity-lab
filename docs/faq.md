<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Frequently Asked Questions (`docs/faq.md`)

**Q1: Does this paper prove $\mathrm{P} \neq \mathrm{NP}$?**  
**No.** $\mathrm{P} \neq \mathrm{NP}$ (`CS-001`) remains completely open. Theorems `T3a` and `T3b` formalize two standard facts in zero-Mathlib Lean 4.35.0: existence and uniqueness of multilinear extensions over arbitrary fields (used in Algebrization) and the counting inequality of the natural-proofs argument. No pseudorandom function, LWE instance or circuit is defined in Lean.

**Q2: Does this paper close $C(2,4,2,2)$ completely?**  
**No.** It proves two complementary obstructions: (1) `T1e` gives a kernel-certified pure-integer 12-variable polymatroid `h_uncond` passing Boolean checks for monotonicity, submodularity (330 orbit representatives) and singleton Ingleton instances at value ratio $8/13 > 3/5$, and (2) `T1f` proves the classical $\mathbb{P}^3$ concurrency fact over arbitrary fields. With the rank routines assumed correct, `T1i`/`T1j` exclude separating inequalities on any 4 single variables, any 5 retrieval objects, or the 6 retrieval objects. Closing the gap $[3/5, 8/13]$, for example via inequalities in 5 or more variables that involve individual storage symbols, or via non-linear schemes, remains open.

**Q3: Why zero-Mathlib Lean 4.35.0 instead of Mathlib?**  
Eliminating Mathlib shrinks the Trusted Computing Base by orders of magnitude, makes clean-room builds finish in seconds without multi-gigabyte `.olean` caches, and enables full independent replay across all six bundled Lean 4.35.0 proof kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) in GitHub Actions CI.

**Q4: Why are there no `native_decide` calls in `PIRCertificates.lean`?**  
`native_decide` introduces the `Lean.ofReduceBool` / `Lean.trustCompiler` compiler-trust axiom, bypassing the kernel. Instead, we compiled the 90 $\mathbb{F}_{11}$ matrix inverse checks (`T1c`) and 330 canonical $S_4$ polymatroid orbits (`T1e`) into $O(\log N)$ balanced binary-tree lookup functions reduced directly inside Lean's kernel via pure `decide` / `rfl`, keeping `T1e` dependent on **`[propext]` alone**.

**Q5: Why is `PalomarChallenge.lean` allowed to contain `sorry`?**  
`lake comparator --config comparator.json --paranoid` judges a `solution_module` (`PalomarSolution.lean`, zero `sorry`) against a statement-only `challenge_module` (`PalomarChallenge.lean`, excluded from `defaultTargets`) to guarantee that every proved theorem matches the challenge specification verbatim. None of `TriadFrontier/*`, `Challenge.lean`, `Solution.lean`, or `PalomarSolution.lean` contain any `sorry`.

**Q6: Has this paper been peer reviewed?**  
Not yet. It is an independent research preprint released with Lean proofs, deterministic multi-language code and falsification tests. An independent statement audit (2026-11-26) found several public claims overstated; the corrections are in `ERRATA.md`.
