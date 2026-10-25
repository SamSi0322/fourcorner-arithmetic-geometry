# Common-coordinate genus and boundary

This source project proves `prop:common-genus-boundary` for the actual normalized
curve of the four literal roots. It proves geometric connectedness and genus nine
as the rank of global Kahler differentials on the actual Qbar pullback; a native
finite ell map to literal Proj P1 of degree sixteen on its actual generic stalks;
exactly the six branch fibres 0, infinity, +(t-1), +(t+1), -(t-1), -(t+1); and no
rational point in those fibres when t>1.

The degree comparison uses field isomorphisms constructed from the original
field-point morphisms on generic stalks. The native generic-stalk square certifies
the function-field pullback of the finite ell map. Every closed-point image is
proved equal to restriction of that same source point's valuation place, including
infinity. The six values are actual closed points on Proj P1 through the constructed
original-X-preserving base isomorphism, with finite and infinity coordinate-order
certificates. No assigned genus or degree, assumed comparison isomorphism, or
replacement rational point is used.

Install this directory as `lean/projects/common_genus` in the accompanying
development tree. It requires sibling `common_exclusion` at `../common_exclusion`,
which already requires the root `fourcorner_paper` and sibling geometric projects.
The 460 reused source modules are pinned individually in
`SHARED_SOURCE_DEPENDENCIES.json`. This payload supplies only the 13 missing proof
modules and one verification entry; no parent copies or compiled artifacts.
No source import adaptation was needed. All 13 proof sources are byte-identical
to their independently reviewed ordinary/cold-checked originals.

With Lean 4.33.1, run `LEAN_NUM_THREADS=1 lake --keep-toolchain build` here. Then run
`lake --keep-toolchain env lean -t0 -Ddebug.skipKernelTC=false Source/CommonGenusPackage.lean`
for the cold verification entry. The entry checks the full statement and prints
transitive axioms for 34 degree, generic-stalk, point, fibre, P1-coordinate and
geometric-differential declarations. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted.

Main declaration:
`FourCorner.CommonGenusBoundaryFull.prop_common_genus_boundary`.

The Lake library owns only its exact top-level module names using explicit
`.one` globs, avoiding ownership of parent namespace prefixes. Nine standard git
dependencies retain their existing pinned revisions in `lake-manifest.json`.
Private paths, historical prompts/logs, and binary caches are excluded.
