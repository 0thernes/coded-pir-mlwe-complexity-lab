# SPDX-License-Identifier: Apache-2.0
# Task runner for coded-pir-mlwe-complexity-lab (Build Standard A31 / B01)

set shell := ["bash", "-euo", "pipefail", "-c"]

default:
	@just --list

reproduce: lean native eshkol python-exact test figures paper citations timestamps

lean:
	cd lean && lake build --wfail && lake env lean VerifyAxioms.lean && lake env lean AuditExhaustiveAxioms.lean && lake env leanchecker Solution && lake env leanchecker PalomarSolution && lake env leanchecker-paranoid Solution && lake env leanchecker-paranoid PalomarSolution

native:
	make -C native clean all test

eshkol:
	node eshkol/run_eshkol_ad.mjs

python-exact:
	PYTHONPATH=python python python/triad_verify/pir_koszul.py
	PYTHONPATH=python python python/triad_verify/polymatroid_barrier.py
	PYTHONPATH=python python python/triad_verify/mlwe_tightness.py
	PYTHONPATH=python python python/triad_verify/complexity_triad.py

test:
	PYTHONPATH=python pytest tests/test_all.py -v

figures:
	PYTHONPATH=python python python/triad_verify/generate_figures.py

paper:
	mkdir -p paper/build
	cd paper && tectonic -X compile main.tex --outdir build --keep-intermediates

citations:
	python scripts/check_citations.py

timestamps:
	python scripts/stamp_timestamps.py --verify

lint:
	ruff check python tests scripts examples
	mypy python/triad_verify scripts --ignore-missing-imports

clean:
	make -C native clean
	rm -rf paper/build lean/.lake .pytest_cache
