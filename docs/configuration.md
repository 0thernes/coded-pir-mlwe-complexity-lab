<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Configuration & Environment Reference (`docs/configuration.md`)

`coded-pir-mlwe-complexity-lab` is completely offline-reproducible (aside from the optional `--online` live HTTP citation audit) and requires **no API keys, credentials, or external services**.

## Environment Variables (see `.env.example`)

| Variable | Default | Purpose |
|---|---|---|
| `CC` | `gcc` (Linux/MinGW) or `clang` | C11 compiler used by `native/Makefile` (`-std=c11 -O2 -Wall -Wextra -Wpedantic -Werror`) |
| `PYTHONPATH` | `python` | Ensures `triad_verify` is importable without editable install |
| `TRIAD_PYTHON` | `python` / `python3` | Python 3.12+ interpreter used by helper scripts |
| `COMPARATOR_BWRAP` | `bwrap` | Path to `bubblewrap` binary on Linux for `lake comparator --paranoid` |
| `CHECK_CITATIONS_ONLINE` | `0` | Set to `1` (or pass `--online`) to query live `doi.org`/`arxiv.org`/`eprint.iacr.org` HTTP status |

## Windows Portability Notes

- On Windows, ensure a GCC toolchain with full C11 `math.h` headers (e.g., MinGW-w64 GCC 14.2.0) is used for `native/` rather than Elan's bundled `clang` (which omits standard C math headers).
- If the repository resides under a path containing square brackets (`[...]`), PowerShell scripts automatically use `-LiteralPath`, and `pytest` should always be invoked from the repository root using the relative path `tests/test_all.py`.
