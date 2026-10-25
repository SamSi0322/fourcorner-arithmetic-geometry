# Common-source matrix theorem

This source project proves the full conditional `thm:cs-matrix`, including
its exact half-weighted certificate equivalence. It also audits the literal
raw rational source exclusion, actual entire H, source-coordinate Kaehler
module pullback of dx/(2y), normalized primitive, actual logarithm values,
and the complete beta/certificate interfaces.

Install as `lean/projects/common_source_matrix`. Its sole direct source
dependency is sibling `common_source` at `../common_source`. Root,
small-curves and EllipticFoundations sources are inherited from that verified
parent. The actual imported cone reuses78 canonical parent source modules
and adds only18 frozen proofs,6 missing support modules and one audit entry.
`SHARED_SOURCE_DEPENDENCIES.json` pins the reused proof sources individually.

Only module file paths and affected import lines are adapted. Existing
FourCorner.CommonSource* references use the parent's CSFoundation mapping;
the one additional CommonSourceDyadicResidue module is moved to CSLogSupport.
Namespaces, declarations, assumptions and all proof bodies remain byte-identical.
`IMPORT_ONLY_ADAPTATION.json` records the original, package and body hashes.

With pinned Lean4.33.1 run `LEAN_NUM_THREADS=1 lake --keep-toolchain --no-cache build`.
Then `lake --keep-toolchain --no-cache env lean -t0 -Ddebug.skipKernelTC=false
-R Source Source/CommonSourceMatrixPackage.lean` audits all critical declarations.
The only permitted transitive axioms are propext, Classical.choice and Quot.sound.
No source exclusion converse, unconditional no-solution theorem, bounded-height
search or replacement of whole H is asserted. Parent sources/configurations and
all9 pinned git dependency revisions are preserved.
