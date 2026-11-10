# LeanDLRA — common commands. Run `make help` for the list.
#
# The library lives in LeanDLRA/ (no `sorry`, zero warnings, standard axioms only).

SHELL := /bin/bash
PY_SCRIPTS := scripts/certificate.py scripts/fidelity.py scripts/gate.py scripts/build_site.py scripts/ledger.py scripts/corpus.py \
              scripts/fetch_arxiv.py scripts/hashdiff.py scripts/connectivity.py scripts/rolling.py scripts/core.py
PYENV := .lake/check/pyenv
# Statement dumps of `make dump`; `make hashdiff` compares the last two (scripts/hashdiff.py).
HASHDIFF := .lake/hashdiff
BEFORE ?= $(HASHDIFF)/before.jsonl.gz
AFTER ?= $(HASHDIFF)/after.jsonl.gz

.DEFAULT_GOAL := help
.PHONY: help deps build catalogue check audit verify index docs site dump hashdiff lint-py test-py ci papers \
        clean

help: ## Show this help
	@grep -E '^[a-zA-Z_-]+:.*?## ' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "  \033[36m%-10s\033[0m %s\n", $$1, $$2}'

deps: ## Download the Mathlib build cache
	lake exe cache get

build: ## Regenerate the root files and build the core library (docs/STRUCTURE.md)
	scripts/gen_root.sh
	uv run -q scripts/core.py check
	lake build LeanDLRA

catalogue: ## Build and check everything, core and catalogue (slow; needs an idle gate)
	scripts/catalogue.sh

check: ## Certify one file: make check FILE=LeanDLRA/Integrators/BUG.lean
	@test -n "$(FILE)" || (echo "usage: make check FILE=<path>"; exit 1)
	scripts/check.sh $(FILE)

audit: ## Core build + axiom audit of the core (what the core workflow of CI runs)
	scripts/gen_root.sh
	scripts/audit.sh

verify: build audit ## Local verification of the core before pushing (build, audit)

index: ## Regenerate the Lean declaration index used by the website (website/decls.json)
	scripts/gen_root.sh
	lake build LeanDLRACatalogue
	lake env lean scripts/DeclIndex.lean

docs: ## Regenerate docs/PROVEN.md and the README status block
	uv run -q scripts/ledger.py

site: index docs ## Generate the website pages into website/ (as the Pages workflow does)
	uv run -q scripts/build_site.py

dump: ## Dump every declaration's type (after `make catalogue`); the previous dump becomes BEFORE
	@mkdir -p $(HASHDIFF)
	uv run -q scripts/hashdiff.py dump $(HASHDIFF)/new.jsonl.gz
	@if [ -f $(AFTER) ]; then mv $(AFTER) $(BEFORE); fi
	@mv $(HASHDIFF)/new.jsonl.gz $(AFTER)

hashdiff: ## Compare the last two dumps (renames: docs/renames.json); MOVE=1 fails on any change
	uv run -q scripts/hashdiff.py diff $(BEFORE) $(AFTER) $(if $(MOVE),--move) --report=$(HASHDIFF)/report.md
	@echo "full report: $(HASHDIFF)/report.md"

lint-py: ## Ruff + ty on the Python scripts
	uvx ruff check scripts/ tests/
	uvx ruff format --check scripts/ tests/
	@test -d $(PYENV) || (uv venv -q $(PYENV) && uv pip install -q --python $(PYENV) fire polars)
	uvx ty check --python $(PYENV) --extra-search-path scripts $(PY_SCRIPTS)

test-py: ## Pytest for the Python scripts (tests/)
	uv run -q --with pytest pytest -q tests

ci: verify lint-py test-py ## Everything the core workflow of CI checks

papers: ## Fetch full texts of the surveyed papers into papers/pdf and papers/txt (local only, git-ignored)
	uv run --script scripts/corpus.py fetch --everything

clean: ## Remove local check artifacts (keeps the Mathlib cache)
	rm -rf .lake/check .lake/build/lib/lean/LeanDLRA
