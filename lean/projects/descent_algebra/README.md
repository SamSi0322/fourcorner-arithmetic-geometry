# Descent Algebra foundations

Author: Yuan Si. License: Apache-2.0.

This source-only Lean project collects independently checked auxiliary algebra
and category-theory foundations. It adds no numbered manuscript result: the
accepted manuscript count remains 55/69. It does not establish a quotient
scheme, AF representability, or a Jacobian/Picard representability theorem.

## Included mathematics

* Finite wide pullbacks for a stable multiplicative morphism property, including
  the empty family, and applications to actual Scheme fibre powers, proper
  morphisms and affine morphisms.
* Coefficients of an actual linear coaction and existence of nonzero invariant
  vectors under the stated counit/coassociativity hypotheses. This does not
  construct a geometric groupoid coaction.
* Flat tensor-kernel and ideal descent, its faithfully-flat tensor-invariance
  wrapper, and the application to global sections of an actual affine flat
  surjective scheme morphism. All stated ring hypotheses are retained.
* Actual stalk-rank comparison from localized module equivalences and finite
  presentation of a finite flat module of constant stalk rank. The exact
  assumptions are the source types; finite presentation is a conclusion.

`Source/DescentAlgebra.lean` imports all thirteen mathematical and compatibility
modules. `Source/DescentAlgebraAudit.lean` checks the twenty-five selected public
interfaces and audits all sixty declarations introduced by those modules for
axioms other than `propext`, `Classical.choice`, and `Quot.sound`. The original
missing-import compatibility wrappers are preserved under `Source/Theorems/`.

## Reproduction

The exact toolchain is Lean 4.33.1. Mathlib is pinned to
`db584cd6d46c92f209a44c0f1c829460d327499d` in both Lake configuration and
`lake-manifest.json`; the latter fixes the transitive dependency revisions.
In an environment with the Lean toolchain and network access to the declared
upstream dependencies, run:

```sh
lake --keep-toolchain --no-cache build DescentAlgebra
lake --keep-toolchain env lean --setup .lake/build/ir/DescentAlgebraAudit.setup.json -t0 -Ddebug.skipKernelTC=false Source/DescentAlgebraAudit.lean
```

The pinned Mathlib sources request Lean 4.33.0, while this project uses Lean 4.33.1.
Build the pinned dependency sources; do not use the upstream 4.33.0 binary cache.

The library deliberately has `roots := #[]` and explicit `.one` module globs.
The build uses Mathlib's `autoImplicit=false` and `maxSynthPendingDepth=3`
options, and enables full kernel type checking. No local binary or private
proof-library dependency is required or included.

## Provenance and validation boundary

`PROVENANCE.json` identifies thirteen sources from four independently reviewed
freezes. Twelve source files are byte-identical. The only adaptation in the
thirteenth is deletion of `import ReplayImports`; every non-import byte is
unchanged. The two standard Mathlib sources that had appeared in a private
replay directory are dependencies of the pinned official Mathlib package,
not owned or redistributed sources.

`API_TYPE_COMPARISON.json` records exact agreement of twenty-five public kernel
types between four separate original frozen provider contexts and the staged
package. Only bound variable names and metadata are erased for comparison;
constants, universes, binder information and expression structure are retained.
`IMPORT_GRAPH.json` describes every direct own-source import. `SOURCE_MANIFEST.json`
binds all fifteen Lean sources, including the new umbrella and unified audit.
`PACKAGE_MANIFEST.json` binds the remaining portable payload.

A fresh Lake build of all fifteen owned sources and entry files passed with the
pinned toolchain. Each of those files also passed a cold kernel check using
`-t0 -Ddebug.skipKernelTC=false`. The audit verified all sixty declarations
introduced by the thirteen source modules and printed the twenty-five public
interface types. `VALIDATION_SUMMARY.json` records the checks and evidence hashes.

The source package also retains its preparatory comparison with the original
frozen contexts. All thirteen mathematical bodies are unchanged. The only source
adaptation removes an unused private aggregate import; the project imports only
its own source modules, pinned Mathlib and Lean.

No binary, cache, private provider path, or unverified draft is part of this
package. Original historical source checks and the private preparatory logs
are retained separately by the maintainer.
