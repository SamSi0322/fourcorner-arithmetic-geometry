# Theta lines of the four-corner curve

Author: Yuan Si. Own code: Apache-2.0. The manuscript and its license are unchanged.

This source-only project proves the complete `thm:theta-lines`. The companion
coverage table records its statement-level acceptance; the published manuscript
and the frozen v1.0.0 archive remain unchanged.

The full endpoint is `FourCorner.ThetaLinesFullAssembly.theta_lines_full`.
It classifies the actual half-canonical bitangent locus, retains repeated-point
half divisors and all projective parameter charts, gives the 28 native lines
and two distinct actual contact points, and identifies the actual odd-theta
finite étale algebra with the specified field product. Its geometric-point
bijection and radical signs use the full absolute Galois action. The actual
original curve, natural global differential restriction, and native divisor
Picard classes are retained.

## Reproduction

The intended installation is `lean/projects/theta_lines` alongside the accepted
`critical_double` and `theta_quotient` packages. These are the only direct local
parents; their declared accepted parent closures supply the shared modules.
No private prototype package or compiled object is a dependency.

Lean is fixed to 4.33.1. Mathlib is fixed to
`db584cd6d46c92f209a44c0f1c829460d327499d`; all transitive revisions are locked.
The pinned Mathlib source requests Lean 4.33.0; this project uses Lean 4.33.1.
Build pinned dependency sources rather than requesting an incompatible upstream
binary cache. With the accepted sibling projects and dependencies present:

```sh
lake --keep-toolchain --no-cache build ThetaLinesProject
lake --keep-toolchain env lean --setup .lake/build/ir/ThetaLinesPortableAudit.setup.json -t0 -Ddebug.skipKernelTC=false Source/ThetaLinesPortableAudit.lean
```

The library has empty roots and explicit `.one` globs, with kernel checking
enabled. Lake explicitly sets `autoImplicit=false` and `maxSynthPendingDepth=3`,
matching every private source replay. `ThetaLinesPortableAudit` audits all declarations introduced by the
132 mathematical and compatibility sources for only `propext`,
`Classical.choice`, and `Quot.sound`. It separately resolves the full type/value closure of all owned declarations.
It traverses the full endpoint type/value
dependency closure and rejects the old arbitrary global bridge and placeholders.

A fresh canonical Lake build and individual cold kernel checks of all 133 owned
source files passed. The full mathematical scope, owner adaptation and runtime
were reviewed independently. `CANONICAL_VERIFICATION.json` records the source
and check hashes; the top-level companion verifier checks the registered endpoint.

## Source and owner preservation

`SOURCE_MANIFEST.json` binds every owned source. Shared accepted sources are
listed in `SHARED_SOURCE_DEPENDENCIES.json` and are not copied. The twelve module-only renames give the eleven bitangent proof files unique
module owners and assign the existing TotallySplit compatibility source the
unique module name `ThetaStdTotallySplit`. Imports are updated accordingly.
Every non-import byte and every mathematical constant namespace is preserved.
The exact mapping and import diffs are recorded in `IMPORT_ONLY_RENAMES.json`
and `IMPORT_ONLY_ADAPTATIONS.json`.

The prototype's two declaration-free rank adapters are replaced by the already
accepted canonical rank owners. The full canonical ring rank, scheme rank and
module-presentation sources have byte-identical non-import bodies to the
corresponding native Mathlib sources. `CANONICAL_NATIVE_OWNER_REDIRECTS.json`
records those source hashes. No new namespace or weakened mathematical body is
used. The narrow prototype audit is replaced by the all-owned audit.

`ENDPOINT_AND_DEFINITIONS_COMPARISON.json` contains compact comparison hashes.
Full original/staged expression evidence remains private. To reproduce the
staged structural hashes without distributing repeated expression strings:

```sh
lake env lean tools/ExportInterfaces.lean > interfaces.log
python3 tools/summarize_interfaces.py interfaces.log
```

This exports a shared expression DAG and hashes its full structural contents.
It preserves constants, universe levels, binder information and definition
values; only bound variable names, metadata and the explicitly recorded
module-private owner prefixes are normalized. Theorem proof terms are not
compared; all theorem types and all non-theorem definition values are compared.

No binaries, caches, machine paths, private documentation, manuscript files,
or publication metadata are included. Upstream source notices and Apache-2.0
licenses are retained.

## Natural global differential boundary

The unchanged legacy `ThetaDGlobalSheafBasis` module contains a valid abstract
linear equivalence derived from dimensions. That equivalence is not claimed
to be natural. Its presence is included in the all-owned axiom/resolution
audit; the separate full paper-endpoint dependency audit strictly rejects it
and the old plane-global bridge. The full theorem uses only the new natural
`ThetaDNaturalGlobalDifferentials.genericGerm` and its actual restriction
diagram on the same original curve. No mathematical body is deleted to pass
either audit.

The complete endpoint type and seven critical actual curve/natural-section/Pic
and algebra definitions match structurally exactly. Across all 2,414 declarations,
47 have reducible typeclass-instance projection spellings that differ: 42 types
and 12 non-theorem values, with overlap. Every one of these 54 closed-expression
comparisons has an actual kernel-checked `rfl` Eq certificate and Std3 axiom result,
recorded by hash in the comparison summary. No arbitrary constant normalization,
weakened proposition, or mathematical body edit is used. Exact old/staged closed
Expr DAGs, Eq statements and rfl terms are preserved privately.

The generic replay checker is `tools/CheckCompatibility.lean`. The maintainer
can provide the structural evidence payload with the SHA256 stated in the
comparison summary and run it via `THETA_COMPAT_PAYLOAD` and `lake env lean`.
This optional provenance replay is not a dependency of the mathematical build.

Every reused parent is tied to its actual owner: 457 same-name modules have
identical native objects, and 43 further same-name modules have identical source
snapshots with different native artifacts. Two declaration-free rank adapters
are replaced by accepted full-copy owners; one canonical module-presentation
dependency has no same-name prototype object. These three rows are not treated
as same-source adapter/native-object comparisons: the actual original native
Rank, FlatRank and ModuleFinitePresentation declaration owners are covered by
the main interface/value gate. The extra parent comparison covers 1,088
declarations and 255 definition values. Four type spellings have kernel-checked
rfl certificates, two already in the main comparison. The combined unique
interface check covers 3,426 declarations, 686 definition values and 56 rfl
certificates. No parent source is copied or private prototype parent selected.
The precise role correction is recorded in `PUBLIC_ADAPTATIONS.json`.

An explicit replay invocation is:

```sh
THETA_COMPAT_PAYLOAD=evidence.json lake env lean -Ddebug.skipKernelTC=false -DautoImplicit=false -DmaxSynthPendingDepth=3 tools/CheckCompatibility.lean
```

The evidence payload is supplied separately by the maintainer and checked
against the SHA256 in the corresponding comparison summary; it is not part
of, or needed by, the mathematical library build.
