#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""Generate data/MANIFEST.sha256, root MANIFEST.sha256, exact_audit_summary.json, and rosette_receipt.json."""

from __future__ import annotations

import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "python"))

from triad_verify.complexity_triad import run_all_triad_checks  # noqa: E402
from triad_verify.mlwe_tightness import run_all_mlwe_checks  # noqa: E402
from triad_verify.pir_koszul import (  # noqa: E402
    koszul_rate_exact,
    lfsr_rate_exact,
    verify_certified_f11_byzantine,
    verify_koszul_rank_grid,
)
from triad_verify.polymatroid_barrier import verify_h_uncond  # noqa: E402


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def write_manifest(manifest_path: Path, rel_paths: list[str], base_dir: Path) -> dict[str, str]:
    lines: list[str] = []
    hashes: dict[str, str] = {}
    for rel in sorted(rel_paths):
        full = base_dir / rel
        if not full.is_file():
            raise FileNotFoundError(f"Expected manifest target missing: {full}")
        digest = sha256_file(full)
        hashes[rel] = digest
        lines.append(f"{digest}  {rel}")
    manifest_path.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    return hashes


def main() -> int:
    version = (ROOT / "VERSION").read_text(encoding="utf-8").strip()

    # 1. Data checksum manifest (Build Standard B39)
    data_files = [
        "f11_byz_witness.json",
        "h_uncond_certified.json",
    ]
    data_hashes = write_manifest(ROOT / "data" / "MANIFEST.sha256", data_files, ROOT / "data")

    # 2. Exact computational audit summary
    grid = verify_koszul_rank_grid()
    f11 = verify_certified_f11_byzantine(ROOT / "data" / "f11_byz_witness.json")
    poly = verify_h_uncond(ROOT / "data" / "h_uncond_certified.json")
    mlwe = run_all_mlwe_checks()
    triad = run_all_triad_checks()

    audit_summary = {
        "schema": "triad-exact-audit/v1",
        "version": version,
        "author": "Alexander S. Donahue",
        "orcid": "0009-0006-8168-9648",
        "pillar_1_cs053": {
            "koszul_6_3_3_rate": str(koszul_rate_exact(6, 3, 3)),
            "lfsr_6_3_3_rate": str(lfsr_rate_exact(6, 3, 3)),
            "koszul_rank_grid": grid,
            "f11_byzantine_rate25": f11,
            "polymatroid_h_uncond": poly,
        },
        "pillar_2_cs026": mlwe,
        "pillar_3_triad": triad,
    }
    (ROOT / "results" / "exact_audit_summary.json").write_text(
        json.dumps(audit_summary, indent=2) + "\n", encoding="utf-8", newline="\n"
    )

    # 3. Root release & proof manifest (Build Standard B37)
    root_targets = [
        "VERSION",
        "data/f11_byz_witness.json",
        "data/h_uncond_certified.json",
        "data/MANIFEST.sha256",
        "dist/Donahue_2026_coded_pir_mlwe_complexity_frontier.pdf",
        "dist/arxiv_submission.tar.gz",
        "lean/Challenge.lean",
        "lean/Solution.lean",
        "lean/PalomarChallenge.lean",
        "lean/PalomarSolution.lean",
        "lean/VerifyAxioms.lean",
        "lean/comparator.json",
        "lean/formalization.yaml",
        "paper/main.tex",
        "paper/refs.bib",
        "results/lean_axioms.txt",
        "results/exact_audit_summary.json",
    ]
    if (ROOT / "results" / "six_kernel_audit.txt").is_file():
        root_targets.append("results/six_kernel_audit.txt")
    root_hashes = write_manifest(ROOT / "MANIFEST.sha256", root_targets, ROOT)

    # 4. Rosette-Wire style deterministic provenance receipt
    receipt = {
        "schema": "rosette-wire-receipt/v1-cleanroom",
        "project": "coded-pir-mlwe-complexity-lab",
        "version": version,
        "generated_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "author": "Alexander S. Donahue",
        "orcid": "0009-0006-8168-9648",
        "lean_toolchain": (ROOT / "lean" / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "data_hashes": data_hashes,
        "artifact_hashes": {
            "pdf": root_hashes["dist/Donahue_2026_coded_pir_mlwe_complexity_frontier.pdf"],
            "arxiv_tarball": root_hashes["dist/arxiv_submission.tar.gz"],
            "lean_axioms": root_hashes["results/lean_axioms.txt"],
            "exact_audit_summary": root_hashes["results/exact_audit_summary.json"],
            "manifest_sha256": sha256_file(ROOT / "MANIFEST.sha256"),
        },
        "all_checks_ok": bool(poly["violations"] == 0 and mlwe["chen_step9"]["all_even_modes_vanish"]),
    }
    (ROOT / "results" / "rosette_receipt.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n"
    )

    print("Generated data/MANIFEST.sha256, MANIFEST.sha256, results/exact_audit_summary.json, results/rosette_receipt.json")
    print(f"PDF SHA-256:     {receipt['artifact_hashes']['pdf']}")
    print(f"Tarball SHA-256: {receipt['artifact_hashes']['arxiv_tarball']}")
    return 0 if receipt["all_checks_ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
