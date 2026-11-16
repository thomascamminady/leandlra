# LeanDLRA — common commands. Run `make help` for the list.
#
# The library lives in LeanDLRA/ (no `sorry`, zero warnings, standard axioms only).

SHELL := /bin/bash
PY_SCRIPTS := scripts/certificate.py scripts/fidelity.py scripts/gate.py scripts/build_site.py scripts/ledger.py scripts/corpus.py \
              scripts/fetch_arxiv.py scripts/hashdiff.py scripts/connectivity.py scripts/rolling.py scripts/core.py \
              scripts/docgen.py scripts/definitions.py
PYENV := .lake/check/pyenv
# Statement dumps of `make dump`; `make hashdiff` compares the last two (scripts/hashdiff.py).
HASHDIFF := .lake/hashdiff
BEFORE ?= $(HASHDIFF)/before.jsonl.gz
AFTER ?= $(HASHDIFF)/after.jsonl.gz
# Pages of docs/ that quote Lean statements. `make docs` writes them from the templates of the same
# name in $(TEMPLATES) (scripts/docgen.py); `make docs-check` compares them with the sources.
TEMPLATES := scripts/templates
DOC_PAGES := docs/GETTING_STARTED.md docs/MAIN_RESULTS.md

.DEFAULT_GOAL := help
.PHONY: help deps build catalogue check audit verify index docs docs-check site dump hashdiff lint-py test-py ci \
        papers clean

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

docs: ## Regenerate the generated pages of docs/ and the README status block (quoted files as committed)
	uv run -q scripts/ledger.py
	uv run -q scripts/docgen.py expand $(TEMPLATES)/GETTING_STARTED.md docs/GETTING_STARTED.md --prefix ../
	uv run -q scripts/docgen.py expand $(TEMPLATES)/MAIN_RESULTS.md docs/MAIN_RESULTS.md --prefix ../
	uv run -q scripts/definitions.py write
	uv run -q scripts/docgen.py check $(DOC_PAGES)

docs-check: ## Compare the pages that quote Lean statements with the sources (writes nothing)
	uv run -q scripts/docgen.py check $(DOC_PAGES)

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
	uv run -q --with pytest --with polars pytest -q tests

ci: verify lint-py test-py ## Everything the core workflow of CI checks

papers: ## Fetch full texts of the surveyed papers into papers/pdf and papers/txt (local only, git-ignored)
	uv run --script scripts/corpus.py fetch --everything

clean: ## Remove local check artifacts (keeps the Mathlib cache)
	rm -rf .lake/check .lake/build/lib/lean/LeanDLRA
