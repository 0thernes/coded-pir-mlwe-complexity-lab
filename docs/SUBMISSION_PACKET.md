<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Pre-Submission Compliance, Disclosure & Archival Packet (`docs/SUBMISSION_PACKET.md`)

Structured release-compliance packet following **Defensible Independent AI Research Playbook v1.3 (Items 37–43)**.

## 1. Fundamental Research & Export-Control Self-Screen (15 CFR § 734.8)

- **Classification:** Basic theoretical mathematics, information theory, lattice-cryptography proof-tightness analysis, and formal verification in Lean 4.35.0.
- **Public-Domain Fundamental Research (15 CFR § 734.7 / § 734.8):** All proofs, C11/Python/Eshkol verification harnesses, and manuscript artifacts are published openly without access restrictions under `Apache-2.0` / `CC-BY-4.0`.
- **Cryptographic Non-Production Scope (ECCN 5D002 Note):** No encryption, decryption, key-agreement, TLS, or network cryptographic protocol binary is implemented or distributed. The C11 constant-time dyadic noise samplers (`triad_dyadic*_sample_ct`) and FIPS 203 `Compress_1` rounding helper are standalone mathematical probability-distribution & integer-arithmetic audit routines (`SECURITY.md`, `LIMITATIONS.md`).
- **Dual-Use Safety Check:** Zero exploit payloads, zero attack tools against deployed systems, and zero biological/chemical/cyber-offensive material.

## 2. Transparent Venue-Specific AI-Assistance Disclosures

Consistent across every archival and publication venue:

- **Preprint / arXiv (`cs.IT` / `cs.CR` / `cs.CC`):**  
  > *This manuscript was conceived, directed, audited, and verified by Alexander S. Donahue (Independent Researcher, ORCID 0009-0006-8168-9648), with AI assistance (Google Antigravity / Gemini) for Lean 4.35.0 proof engineering, multi-language computational verification harnesses, figure production, and AMS-LaTeX typesetting. Every formal theorem is independently machine-checked with zero `sorry` and zero `native_decide` across six Lean 4.35.0 proof kernels; the human author bears sole responsibility for all statements, claims, and boundaries.*
- **Zenodo / Software Heritage / GitHub Release:**  
  Full source repository, frozen PDF, clean-room `arxiv_submission.tar.gz`, SHA-256 `MANIFEST.sha256`, DigiCert RFC 3161 `.tsr`, and 3-calendar Bitcoin OpenTimestamps `.ots` are deposited openly; AI-assisted proof engineering is explicitly disclosed in `README.md`, `LIMITATIONS.md`, `lean/formalization.yaml`, and `paper/main.tex` in compliance with Zenodo depositor transparency policies.
- **Mathlib / Formal Verification Submission Note:**  
  Zero Mathlib dependencies by design (minimal Palomar TCB). Any future upstream port of characteristic-free `StrassenWinograd.lean`, `BrockettDobkin.lean`, `AlgebraicComplexity.lean`, or `PaleyCapacity.lean` to Mathlib4 will follow Mathlib's AI-disclosure PR guidelines and native Mathlib `Matrix`/`MvPolynomial` APIs.
- **External Endorsement & Peer-Review Honesty:**  
  No external DOI, journal acceptance, or arXiv endorsement is fabricated or implied prior to actual venue receipt.

## 3. Withdrawal, Correction & Versioning Policy

- Confirmed mathematical or formalization errors are **never silently deleted**: they are logged permanently in [`ERRATA.md`](../ERRATA.md) with affected version tags, root cause, and fixed commit hash, and released as a new semantic version (`CHANGELOG.md`, `VERSION`).
- Pre-release findings from internal hardening cycles are preserved permanently in [`HARDENING_LOG.md`](../HARDENING_LOG.md) using the Build Standard v1.2.0 10-class taxonomy.

## 4. Palomar & Long-Term Preservation Checklist

- [x] `lean/lean-toolchain` pinned to `leanprover/lean4:v4.35.0` (exact commit-pinned `lake-manifest.json`).
- [x] `lean/PalomarChallenge.lean` (excluded from `defaultTargets`) & `lean/PalomarSolution.lean` match `lean/comparator.json` verbatim.
- [x] `lake build --wfail` (0 warnings), `VerifyAxioms.lean` (35 decls), `AuditExhaustiveAxioms.lean` (`1,656` `TriadFrontier.*` decls under `module`), 6-kernel replay (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche --verified` 4,745 decls, `con-ron --verified` 4,745 decls), plus live negative kernel-rejection tamper gate.
- [x] Clean-room `dist/arxiv_submission.tar.gz` compiles from scratch via `tectonic -X compile main.tex` with 0 Overfull / 0 Float-too-large / 0 Undefined warnings.
- [x] Dual cryptographic timestamps (`data/MANIFEST.sha256.tsr` RFC 3161 + `data/MANIFEST.sha256.ots` 3-calendar Bitcoin OpenTimestamps) verified in CI (`scripts/stamp_timestamps.py --verify`) + GitHub SLSA Sigstore build provenance (`actions/attest-build-provenance@v2`).
- [x] Registered as immutable entry **`0TH-2026-012`** in `0thernes-research-archive` with pinned submodule commit, frozen PDF copy, SHA-256 checksums, and Software Heritage snapshot trigger.
