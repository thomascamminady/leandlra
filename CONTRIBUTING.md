# Contributing to LeanDLRA

Thank you for considering a contribution. This page says how a change reaches `main` and what a
change has to satisfy. The detailed rules are in [docs/CONVENTIONS.md](docs/CONVENTIONS.md); the
steps for a new result are in
[Getting started, section 6](docs/GETTING_STARTED.md#6-how-to-add-a-result); the task-oriented
[Guide](docs/GUIDE.md) says where things are.

## Workflow

1. Fork the repository and make a branch.
2. Build the core once: `lake exe cache get`, then `make build`.
3. Make the change; check single files while you work (below).
4. Run `make verify` (build and audit of the core). Run `make ci` if you changed anything in
   `scripts/` or `tests/`; it adds the Python checks. If you changed a page of `docs/` that quotes
   Lean statements, run `make docs` and commit the result.
5. Open a pull request against `main`. The core workflow of CI
   (`.github/workflows/lean_action_ci.yml`) runs on every push and pull request; the catalogue
   workflow runs on `main`.
6. The maintainers merge. Changes to Lean files go through the gate (`scripts/gate.py`), which
   builds the changed files with warnings as errors, builds the core and audits the core and the
   changed files, and checks the recorded statements. A change that fails one of these steps is
   not merged, and the maintainers say which step failed.

## What a change has to satisfy

* **No placeholders.** No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`
  or `unsafe`. `scripts/audit.sh` searches the sources for them.
* **Standard axioms only.** Every constant depends on `propext`, `Classical.choice` and
  `Quot.sound` and on nothing else; the audit checks this, private constants included.
* **Zero warnings.** The build uses warnings as errors, Mathlib's style linters included. Lines
  have at most 100 characters.
* **A core module imports core modules only.** The core is the set of modules imported by
  `LeanDLRA.lean`; the catalogue (folders `Literature`, `OpenProblems`, `Novel`, `Corrections`)
  is built separately. `make build` runs `scripts/core.py check`. See
  [docs/STRUCTURE.md](docs/STRUCTURE.md). No `import Mathlib` in library files: import the
  modules that you use.
* **Recorded statements do not change.** `docs/statements.json` records the elaborated type of
  the statements that were fixed before they were proved. A theorem recorded there keeps its
  type. If the library needs another form, add a new theorem and prove the recorded one from it,
  with its original statement. A rename of a constant is entered in `docs/renames.json`
  (`scripts/fidelity.py` reads it); a rename leaves a deprecated alias.
* **One definition per concept.** Search [docs/DEFINITIONS.md](docs/DEFINITIONS.md),
  [docs/CONCEPTS.md](docs/CONCEPTS.md) and Mathlib before you define anything; use what exists.
  Definitions go into the `Defs.lean` of their folder, with a basic API and an `example`
  that shows that a structure can be satisfied ([docs/CONVENTIONS.md](docs/CONVENTIONS.md),
  section 3).
* **A theorem has hypotheses that can be met.** A new structure or main theorem gets an `example`
  that satisfies all its hypotheses, with data for which the statement is not trivial.
* **Names and notation.** Mathlib conventions; the name of a theorem says what it bounds or
  states; notation and hypotheses as in sections 4 to 7 of the conventions. The Frobenius norm is
  available only inside `open scoped LeanDLRA.Frobenius`.
* **Docstrings.** Every file starts with a module docstring in the layout of section 8 of the
  conventions, and every public declaration has a docstring written in words. Papers are cited
  by the key of `docs/references.bib`, in the form of section 9.
* **No claims of novelty** in a docstring or a page unless the literature check supports
  them; say what a theorem states and cite the source of a result that is known.
* **Results of single papers** that are not stated in the core definitions belong to the
  catalogue ([docs/CONVENTIONS.md](docs/CONVENTIONS.md), section 10).

[docs/CONVENTIONS.md](docs/CONVENTIONS.md), section 13, is a checklist for a new or moved file.

## Checking while you work

| Command | What it does |
|---|---|
| `scripts/fc --axioms FILE.lean` | checks one file against the compiled library without building anything; with `--axioms` it also fails on any axiom beyond the standard ones |
| `make check FILE=LeanDLRA/Path/File.lean` | certifies one file: no errors, no warnings, no placeholders, standard axioms only |
| `make build` | regenerates the root files, checks the import rule, builds the core |
| `make audit` | builds the core and audits every constant for axioms |
| `make verify` | `build` and `audit` |
| `make ci` | `verify` and the checks and tests of the Python scripts (`ruff`, `ty`, `pytest`) |
| `make docs`, `make docs-check` | regenerate the pages that quote Lean statements; compare them with the sources |
| `make help` | list all targets |

Python scripts of the repository are run with `uv` (`uv run -q scripts/NAME.py`), and take their
arguments through `fire`.

## Documentation and examples

* A page of `docs/` that quotes Lean statements is generated from a template in
  `scripts/templates/` by `make docs`; edit the template and not the page.
  [docs/GUIDE.md](docs/GUIDE.md) is one of them.
* The folder `Examples/` holds worked examples that apply the theorems of the core to concrete
  problems. They are a separate library (`lake build Examples`), not part of the core, and are
  written to be read from top to bottom. An example may define concrete data; it states no
  new result. If you change a core theorem that an example uses, update the example.

## Questions

Open an issue before a large change (a new integrator, a move of many files), so that the place
and the definitions to reuse can be agreed first.
