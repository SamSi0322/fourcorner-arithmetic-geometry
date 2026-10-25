# Unramified genus-seventeen covers

This source project proves the complete `prop:common-genus17` on actual canonical
curves and their native finite covers to the same accepted D_t. For every twist in
the exact finite K_t, it proves geometric connectedness, actual generic-stalk
degree two, and genus seventeen as global Kahler rank on the actual Qbar pullback.
Unramifiedness records a finite separable generic extension and, at every actual
closed point including infinity, same-place restriction, index one and finite
separable residue extension.

Every actual Q-point of D_t lifts on one global twist in this exact K_t. The
native cover returns that original point, and all five literal ordered functions
ell,P,C,M,B have actual stalk representatives with the original values. The fifth
root has the literal equation Z^2=ell/kappa and a positive rational stalk value.
The geometry and lifting use the same frozen field, model and cover definitions.

Install as `lean/projects/common_genus17` in the accompanying development tree.
Its only direct source dependency is sibling `common_genus` at `../common_genus`;
that package retains the existing canonical parents. Individual required parent
proof hashes are pinned in `SHARED_SOURCE_DEPENDENCIES.json` and were reconciled
against the verified source packages. No parent proof copies or compiled artifacts
are included. The 36 supplied proof/support sources are byte-identical to their
frozen ordinary/cold checked originals, with no import adaptations. One additional
verification entry prints every declaration listed in `AUDIT_DECLARATIONS.json`.

With Lean 4.33.1 run `LEAN_NUM_THREADS=1 lake --keep-toolchain --no-cache build`,
then `lake --keep-toolchain --no-cache env lean -t0 -Ddebug.skipKernelTC=false -R Source Source/Genus17Package.lean`.
The same cold command on `Source/Genus17Full.lean` checks the full statement.
Only propext, Classical.choice and Quot.sound are permitted in the audited
transitive axiom lists. The library owns only its exact top-level module names
through explicit `.one` globs. Nine standard git dependencies retain their pinned
revisions; no downloads, private paths, historical prompts/logs or binaries are
part of this payload.

Main declaration: `FourCorner.CommonGenus17Full.common_genus17`.
