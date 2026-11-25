<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Security Policy

## Scope

This repository is a mathematical research, formal verification (Lean 4.35.0), and reference verification codebase. **The native C11 and Python routines are mathematical verification artifacts, NOT constant-time production cryptographic libraries** and must not be deployed directly in production TLS/KEM key-exchange paths.

## Reporting a Vulnerability or Mathematical Soundness Defect

If you discover:
- A soundness defect, vacuity issue, or unpermitted axiom in `lean/`,
- A memory safety or undefined-behavior bug in `native/`,
- A counterexample falsifying any claim in `CLAIMS.md` or `paper/main.tex`,

please report it either via a GitHub Issue or privately by email to `0_0@0thernes.art` (Alexander S. Donahue, ORCID `0009-0006-8168-9648`). Confirmed soundness defects are documented transparently in `ERRATA.md` and `HARDENING_LOG.md`.
