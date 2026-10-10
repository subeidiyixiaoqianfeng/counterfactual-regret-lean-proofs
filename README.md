# Lean proof artifact

This repository contains 102 Lean source modules with 816 theorem/lemma declarations, together with a map of 13 numbered mathematical results from the accompanying manuscript.

## Reading the proofs

- `PaperResults.lean` is the import root for the publication dependencies.
- `PAPER_RESULTS.json` maps numbered results to Lean declarations and states their assumptions.
- `PAPER_COVERAGE.json` records the formalization scope.
- The other `.lean` files contain the definitions and proofs.

## Reproducing verification

Use Lean **4.19.0** and a built mathlib checkout at revision **c44e0c8ee63ca166450922a373c7409c5d26b00b**.
Runtime and dependency binaries are not included. Install the matching toolchain, obtain that mathlib revision, and build its dependencies before running this artifact.

Set `DRGPR_LEAN_BIN` to the full path of the Lean executable and `DRGPR_MATHLIB_ROOT` to the full path of the built mathlib checkout. Then run from this directory:

```sh
python3 verify_all.py
```

Set `DRGPR_FORCE_REBUILD=1` to force checking all local modules. The script compiles modules in dependency order and writes logs and a report to `fresh_audit/`.

## Included verification evidence

`verification-evidence.zip` contains the supplied compilation logs and `fresh_audit/BUILD.json`. All 102 source hashes and 102 log hashes were checked against that manifest during packaging. The Lean sources are byte-for-byte unchanged. The verification script was made portable by requiring explicit compiler and mathlib paths.

Packaging did not recompile the proofs. The supplied manifest records 816 theorem/lemma declarations and only the axioms `propext`, `Classical.choice`, and `Quot.sound`. `SHA256SUMS` lists the files in this artifact.

## Scope

The proofs establish mathematical results under the stated models, interfaces, and assumptions. They do not verify arbitrary deployed LLM software, automatic equivalence between prose and Lean statements, or the Lean compiler itself.
