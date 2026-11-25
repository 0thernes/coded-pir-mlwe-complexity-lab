<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# ADR 0002: Independent Researcher Attribution & Dual Apache-2.0 / CC-BY-4.0 Licensing

- **Status:** Accepted (2026-11-25)
- **Context:** Independent scholarly preprints benefit from clear individual researcher attribution without ambiguity over corporate entity claims, and from pairing a permissive patent-safe software license with a standard scholarly documentation license.
- **Decision:** Standardize author attribution across the manuscript, `CITATION.cff`, `formalization.yaml`, `pyproject.toml`, and all repository docs to `Alexander S. Donahue (Independent Researcher, Spokane, WA, USA; ORCID 0009-0006-8168-9648; email 0_0@0thernes.art)`, and apply dual licensing via `REUSE.toml`: `Apache-2.0` (`LICENSE`) for all source code, Lean proofs, and scripts, and `CC-BY-4.0` (`LICENSE-DOCS`) for the white paper, figures, data tables, and prose documentation.
- **Consequences:** Zero corporate-entity affiliation drift anywhere in the repository; machine-readable SPDX compliance across every tracked file.
