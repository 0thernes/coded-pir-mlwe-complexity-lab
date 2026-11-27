#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""Generate data/MANIFEST.sha256, complete root MANIFEST.sha256, exact_audit_summary.json, and rosette_receipt.json."""

from __future__ import annotations

import hashlib
import json
import sys
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "python"))

from triad_verify.complexity_triad import run_all_triad_checks
from triad_verify.mlwe_tightness import run_all_mlwe_checks
from triad_verify.pir_koszul import (
    koszul_rate_exact,
    lfsr_rate_exact,
    verify_certified_f11_byzantine,
    verify_koszul_rank_grid,
)
from triad_verify.polymatroid_barrier import (
    verify_4var_i4_and_5obj_f2_realizability,
    verify_6obj_f2_64_realization,
    verify_h_uncond,
)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def write_manifest(manifest_path: Path, rel_paths: list[str], base_dir: Path) -> dict[str, str]:
    lines: list[str] = []
    hashes: dict[str, str] = {}
    for rel in sorted(set(rel_paths)):
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
    t1i_lin = verify_4var_i4_and_5obj_f2_realizability(ROOT / "data" / "h_uncond_certified.json")
    t1j_f2 = verify_6obj_f2_64_realization(ROOT / "data" / "h_uncond_certified.json")
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
            "t1i_linear_realizability": t1i_lin,
            "t1j_6obj_f2_64_realization": t1j_f2,
        },
        "pillar_2_cs026": mlwe,
        "pillar_3_triad": triad,
    }
    (ROOT / "results" / "exact_audit_summary.json").write_text(
        json.dumps(audit_summary, indent=2) + "\n", encoding="utf-8", newline="\n"
    )

    # 3. Complete root release, proof, native, Eshkol, Python, paper & figure manifest (Build Standard B37)
    lean_files = sorted(
        p.relative_to(ROOT).as_posix()
        for p in (ROOT / "lean").rglob("*.lean")
        if ".lake" not in p.parts
    )
    figure_files = sorted(
        p.relative_to(ROOT).as_posix()
        for p in (ROOT / "paper" / "figures").glob("fig*.pdf")
    )
    py_core_files = sorted(
        p.relative_to(ROOT).as_posix()
        for p in (ROOT / "python" / "triad_verify").glob("*.py")
    )
    eshkol_files = sorted(
        p.relative_to(ROOT).as_posix()
        for p in (ROOT / "eshkol").iterdir()
        if p.is_file() and p.suffix in {".esk", ".mjs"}
    )
    root_targets = (
        [
            "VERSION",
            "CITATION.cff",
            "ERRATA.md",
            "repo.yaml",
            "repo-standard.schema.json",
            "data/f11_byz_witness.json",
            "data/h_uncond_certified.json",
            "data/MANIFEST.sha256",
            "dist/Donahue_2026_coded_pir_mlwe_complexity_frontier.pdf",
            "dist/arxiv_submission.tar.gz",
            "docs/site/index.html",
            "docs/site/blueprint.html",
            "lean/comparator.json",
            "lean/formalization.yaml",
            "lean/lake-manifest.json",
            "lean/lakefile.toml",
            "lean/lean-toolchain",
            "native/include/triad_core.h",
            "native/src/triad_core.c",
            "native/src/triad_cli.c",
            "paper/main.tex",
            "paper/refs.bib",
            "results/lean_axioms.txt",
            "results/exact_audit_summary.json",
        ]
        + lean_files
        + figure_files
        + py_core_files
        + eshkol_files
    )
    if (ROOT / "results" / "six_kernel_audit.txt").is_file():
        root_targets.append("results/six_kernel_audit.txt")
    root_hashes = write_manifest(ROOT / "MANIFEST.sha256", root_targets, ROOT)

    # 4. Rosette-Wire style deterministic provenance receipt
    artifact_hashes: dict[str, str] = {
        "pdf": root_hashes["dist/Donahue_2026_coded_pir_mlwe_complexity_frontier.pdf"],
        "arxiv_tarball": root_hashes["dist/arxiv_submission.tar.gz"],
        "lean_axioms": root_hashes["results/lean_axioms.txt"],
        "exact_audit_summary": root_hashes["results/exact_audit_summary.json"],
        "manifest_sha256": sha256_file(ROOT / "MANIFEST.sha256"),
        "manifest_entries": str(len(root_hashes)),
    }
    receipt: dict[str, Any] = {
        "schema": "rosette-wire-receipt/v1-cleanroom",
        "project": "coded-pir-mlwe-complexity-lab",
        "version": version,
        "generated_utc": datetime.now(UTC).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "author": "Alexander S. Donahue",
        "orcid": "0009-0006-8168-9648",
        "lean_toolchain": (ROOT / "lean" / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "data_hashes": data_hashes,
        "artifact_hashes": artifact_hashes,
        "all_checks_ok": bool(poly["violations"] == 0 and mlwe["chen_step9"]["all_even_modes_vanish"]),
    }
    (ROOT / "results" / "rosette_receipt.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n"
    )

    print(
        f"Generated data/MANIFEST.sha256 ({len(data_hashes)} files), "
        f"MANIFEST.sha256 ({len(root_hashes)} files), exact_audit_summary.json, rosette_receipt.json"
    )
    print(f"MANIFEST SHA-256: {artifact_hashes['manifest_sha256']}")
    print(f"PDF SHA-256:      {artifact_hashes['pdf']}")
    print(f"Tarball SHA-256:  {artifact_hashes['arxiv_tarball']}")
    return 0 if receipt["all_checks_ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
