<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Upgrading & Versioning Policy (`UPGRADING.md`)

`coded-pir-mlwe-complexity-lab` follows [Semantic Versioning 2.0.0](https://semver.org/) with `VERSION` as the single source of truth.

- **Patch releases (`x.y.z`):** Documentation clarifications, CI maintenance, or non-breaking script fixes. All theorem statements (`T1a`–`T3h`) in `lean/Challenge.lean` and `lean/PalomarChallenge.lean` remain strictly unchanged.
- **Minor releases (`1.x.0`):** Additional machine-checked theorems, newly certified finite-field PIR witnesses, or extended computational verifiers. Existing theorem names and Python/C11 public functions remain backward-compatible.
- **Major releases (`x.0.0`):** Changes to theorem statement signatures in `Challenge.lean` or breaking CLI/API changes. Any errata affecting published theorems will be logged transparently in [`ERRATA.md`](ERRATA.md) and [`CHANGELOG.md`](CHANGELOG.md).
