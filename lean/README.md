# Lean companion — release 1.0.0

Author of the manuscript: Yuan Si.

This snapshot contains complete formal proofs of 34 of the paper's 69 numbered
statements, together with supporting lemmas. `coverage.csv` and `coverage.json`
identify every complete statement and its exact Lean declarations. Formalization
of the remaining statements is continuing.

## Environment

Lean: leanprover/lean4:v4.33.1.
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.
Dependency revisions are locked in each `lake-manifest.json`.
The pinned mathlib source requests Lean 4.33.0; its public binary cache cannot be
used by Lean 4.33.1. Keep this project's compiler and build dependency sources.

## Reproduce

Install elan and the pinned toolchain. The included manifests pin dependency
revisions. From this directory run:

```sh
python3 verify.py
```

The verifier builds all four projects and runs cold kernel checks with `lean -t0`.
It checks printed axiom lists against `propext`, `Classical.choice`, `Quot.sound`.
Reports are written to `verification/`. Each companion is also buildable through
its own ordinary Lake project; `projects.json` records exact targets and audits.
No prebuilt `.olean` files or local `.lake` caches are distributed.

## Licenses and provenance

Original project code is Apache-2.0. Third-party files keep their original
copyright notices and licenses. The elliptic foundations combine the pinned
Mordell–Weil and reduction libraries documented in `UPSTREAM_PROVENANCE.json`
beside each vendor copy. A subset of a dependency is included for these proofs;
the package does not claim to formalize the full named upstream project.

The manuscript PDF and LaTeX are CC BY 4.0. See the release-level LICENSES file.
