#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""Verify BibTeX bibliography integrity and optionally live-check every DOI / arXiv / URL."""
from __future__ import annotations

import argparse
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
BIB_PATH = REPO_ROOT / "paper" / "refs.bib"


def parse_bib(text: str) -> list[dict]:
    entries: list[dict] = []
    pattern = re.compile(r"@(\w+)\s*\{\s*([^,\s]+)\s*,")
    matches = list(pattern.finditer(text))
    for idx, m in enumerate(matches):
        start = m.end()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(text)
        body = text[start:end]
        fields: dict[str, str] = {}
        for fm in re.finditer(r"(\w+)\s*=\s*(?:\{((?:[^{}]|\{[^{}]*\})*)\}|\"([^\"]*)\"|(\d+))", body):
            k = fm.group(1).lower()
            v = fm.group(2) if fm.group(2) is not None else (fm.group(3) if fm.group(3) is not None else fm.group(4))
            fields[k] = v.strip()
        entries.append({"type": m.group(1).lower(), "key": m.group(2), "fields": fields})
    return entries


def check_url(url: str, timeout: float = 12.0) -> tuple[bool, str]:
    headers = {"User-Agent": "TriadFrontier-CitationAudit/1.0 (+https://github.com/0thernes/coded-pir-mlwe-complexity-lab)"}
    for method in ("HEAD", "GET"):
        req = urllib.request.Request(url, headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                code = resp.getcode()
                if 200 <= code < 400:
                    return True, f"HTTP {code}"
        except urllib.error.HTTPError as exc:
            if exc.code in (403, 405, 429) and method == "HEAD":
                continue
            return False, f"HTTP {exc.code}"
        except (urllib.error.URLError, TimeoutError, OSError) as exc:
            if method == "HEAD":
                continue
            return False, str(exc)
    return False, "unreachable"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--online", action="store_true")
    args = parser.parse_args()
    entries = parse_bib(BIB_PATH.read_text(encoding="utf-8"))
    keys = [e["key"] for e in entries]
    errors: list[str] = []
    dups = {k for k in keys if keys.count(k) > 1}
    if dups:
        errors.append(f"Duplicate BibTeX keys: {sorted(dups)}")
    for e in entries:
        for req in ("author", "title", "year"):
            if not e["fields"].get(req):
                errors.append(f"{e['key']}: missing '{req}'")
    tex_files = sorted((REPO_ROOT / "paper").rglob("*.tex"))
    cited: set[str] = set()
    for tf in tex_files:
        txt = tf.read_text(encoding="utf-8")
        for cm in re.finditer(r"\\cite[a-zA-Z]*\*?(?:\[[^\]]*\])*\{([^}]+)\}", txt):
            for raw_k in cm.group(1).split(","):
                k = raw_k.strip()
                if k:
                    cited.add(k)
                    if k not in set(keys):
                        errors.append(f"{tf.name}: undefined citation '{k}'")
    print(f"Parsed {len(entries)} BibTeX entries; checked {len(tex_files)} .tex files ({len(cited)} unique citations).")
    if args.online:
        for e in entries:
            f = e["fields"]
            target = None
            if f.get("doi"):
                doi = f["doi"].replace("https://doi.org/", "").strip()
                target = f"https://doi.org/api/handles/{doi}"
            elif f.get("eprint"):
                target = f"https://arxiv.org/abs/{f['eprint'].strip()}"
            elif f.get("url"):
                target = f["url"].strip()
            if target:
                ok, status = check_url(target)
                print(f"  [{'OK' if ok else 'FAIL'}] {e['key']}: {target} -> {status}")
                if not ok:
                    errors.append(f"{e['key']}: {target} -> {status}")
    if errors:
        for err in errors:
            print(f"ERROR: {err}", file=sys.stderr)
        return 1
    print("Citation audit PASSED.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
