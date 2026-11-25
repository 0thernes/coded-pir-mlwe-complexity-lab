<!-- SPDX-License-Identifier: Apache-2.0 -->
# Gemini / Antigravity Agent Instructions (`GEMINI.md`)

Canonical project instructions live in [`AGENTS.md`](AGENTS.md). Follow every rule in `AGENTS.md`, plus:
- On Windows paths containing brackets, always pass `-LiteralPath` to PowerShell cmdlets and invoke `pytest` from the repository root with relative paths (`tests/test_all.py`).
- After editing `paper/main.tex`, compile with Tectonic (`--keep-logs`), confirm zero overfull hboxes, visually inspect modified PDF pages, and re-verify `dist/arxiv_submission.tar.gz` in a clean temporary directory.
- After modifying any verified data or release artifact, regenerate manifests via `python scripts/make_manifest.py`.
