# Lean companion — postpublication development

Author of the manuscript: Yuan Si.

This snapshot contains complete formal proofs of 43 of the paper's 69 numbered
statements, together with supporting lemmas. `coverage.csv` and `coverage.json`
identify every complete statement and its exact Lean declarations. Formalization
of the remaining statements is continuing. The published v1.0.0 snapshot remains
at 34 of 69 statements.

The new complete norm lemma is `FourCorner.HasseNorms.hp_norms`. Its proof
constructs the quadratic norm criterion using Euclidean division in the
integer square-root-of-two ring; it assumes no global reciprocity axiom.
`HasseNormsInterface.lean` also proves the literal local-source equivalence
and the field-norm criterion for every rational scalar.

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

The verifier builds every project in `projects.json` and runs cold kernel checks
with `lean -t0`.
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

The two genus-five companion projects prove the complete opposite and adjacent
fixed-distance curve propositions. The opposite proof uses the actual literal
projective intersection; the adjacent proof constructs the actual finite
normalization cover in the ordered conic field extension. Both identify the
geometric genus using global Kähler differentials on the categorical base change.
The adjacent package reuses the opposite package’s pinned source foundations.

The common-curve projects verify the genus-nine curve and its actual degree-sixteen
map, all six branch fibres and rational-boundary exclusions. They also prove the
complete-curve residue-matrix exclusion and the explicit infinite family, with
real chamber coordinates tied to points on the same rational models. Fixed
finite-field and fixed-matrix subclaims use kernel-checked finite decisions;
the global parameter and height quantifiers are retained.

The genus-seventeen package proves the exact finite twist domain and the complete
same-point rational lifting statement. Its covers have actual generic degree two
and genus seventeen after base change; unramifiedness is verified at every curve
place, including infinity, with the residue extensions and their separability.
The four original roots retain their signs, and the added equation is exactly
`Z^2 = ell/kappa`.

The common-source package proves both branches of the odd-prime row lemma on the
actual rational elliptic group. Its characters use the reduction image of the
entire subgroup, and its exclusions retain all compensation points and every
valuation depth. The original ordered-source and reduction maps are checked.

The common-source matrix package identifies the normalized integral of the
original curve differential through its native coordinate ring and Kähler
pullback. It proves the whole-subgroup logarithmic character comparison and
combines the exact source coset with all odd-prime rows. The resulting theorem
includes both the source exclusion and the precise certificate equivalence.
