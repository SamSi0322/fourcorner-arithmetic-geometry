# Common-coordinate exclusion and explicit infinite family

This source project proves the full residue-matrix exclusion theorem and its
explicit infinite-family corollary. Rational emptiness concerns actual points on
the native complete normalization curve. The same-point extraction preserves
ell and all four ordered roots through actual stalk and residue maps. The real
points in the family lie on the same curves, with the chamber coordinates proved
to be actual regular-section pullback values.

Install this directory as `lean/projects/common_exclusion` in the accompanying
development tree. Its source dependencies are the root `fourcorner_paper` project
at `../..` and sibling `adjacent_genus` at `../adjacent_genus`; the latter depends
on sibling `opposite_genus`. Required shared source hashes are recorded in
`SHARED_SOURCE_DEPENDENCIES.json`. No root FourCorner module imports this project.

With Lean 4.33.1, run `LEAN_NUM_THREADS=1 lake --keep-toolchain build` here. The
`CommonExclusionPackage` entry point checks both full statements and prints the
transitive axioms for their actual source, boundary, scheme, and real-point
identities. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
After building, run
`lake --keep-toolchain env lean -t0 -Ddebug.skipKernelTC=false Source/CommonExclusionPackage.lean`
for the cold entry check.

Main declarations:
- `FourCorner.CommonExclusion.common_exclusion`
- `FourCorner.CommonInfinite.common_infinite`

This payload contains 57 missing proof/support modules and one verification
entry. It reuses 43 root arithmetic sources and 415 geometric sources instead
of copying them. Its manifest records exact source hashes. Logs, private paths,
historical attempts, and custom compiled artifacts are excluded.

Two newly supplied arithmetic modules use top-level module paths to avoid the
root library's `FourCorner` module glob. Only two import lines are adapted;
all theorem definitions and proof bodies are unchanged. The source manifest
records the original hashes and this import-only packaging adjustment.

The proofs at 37 use kernel-checked finite decisions for fixed finite-field
identities and nonsquareness checks. The explicit six-prime family matrix uses
a kernel-checked finite decision for its fixed F_2 kernel, followed by a
rank-nullity proof of rank five. These finite checks do not search over bounded
rational heights; the exclusion theorem applies without a height bound.
