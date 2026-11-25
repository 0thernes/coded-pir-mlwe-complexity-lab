<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Operations, Archival Backups & Mirroring (`docs/operations.md`)

This repository is a static scientific research artifact with no runtime servers, databases, or user-data storage. Operations focus exclusively on deterministic build reproduction, cryptographic integrity, offsite mirroring, and long-term archival preservation.

## Routine Integrity Verification

```bash
# Re-verify all checksums
sha256sum -c data/MANIFEST.sha256
sha256sum -c MANIFEST.sha256

# Re-verify README axiom block parity against results/lean_axioms.txt
python scripts/check_readme_axioms.py

# Re-run full verification suite
just reproduce
```

## Offsite Repository Mirror & Cold `git bundle` Backup (Build Standard A35)

To create a self-contained cold backup archive and verify offsite mirror parity:

```bash
# Create full-history cold backup bundle (all branches and tags)
git bundle create ../coded-pir-mlwe-complexity-lab-v1.0.0.bundle --all
git bundle verify ../coded-pir-mlwe-complexity-lab-v1.0.0.bundle
sha256sum ../coded-pir-mlwe-complexity-lab-v1.0.0.bundle

# Mirror to a secondary remote or archival repository
git clone --mirror https://github.com/0thernes/coded-pir-mlwe-complexity-lab.git
```

## Master Archive Registration & Preservation

Every frozen release is registered as an immutable pinned submodule + frozen PDF + SHA-256 checksum dossier in [`0thernes-research-archive`](https://github.com/0thernes/0thernes-research-archive) under identifier **`0TH-2026-012`**, with GitHub Actions SLSA build provenance attestation (`actions/attest-build-provenance@v2`) attached to `dist/Donahue_2026_coded_pir_mlwe_complexity_frontier.pdf` and `dist/arxiv_submission.tar.gz`.
