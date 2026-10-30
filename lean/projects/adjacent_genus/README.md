# Adjacent normalized cover: geometric connectedness and genus five

This source project proves the complete normalized-cover proposition for every rational
`c > 0`, `c ≠ 1`, using an actual finite normalization Scheme morphism in the original
conic function-field extension. It also computes the global relative Kähler sections
of the actual geometric pullback.

Place this directory beside the canonical `opposite_genus` source project. Its exact
source manifest and the hashes of all required shared modules are recorded in
`SHARED_SOURCE_DEPENDENCY.json`; shared source is intentionally not copied here.
The dependency supplies the pinned Mathlib revision and prior geometric foundations.

Use Lean 4.33.1 and run `LEAN_NUM_THREADS=1 lake --keep-toolchain build` from this directory.
The `AdjacentGenus` entry point prints the full theorem and its transitive axiom list.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.

The main declaration is
`FourCorner.AdjacentNormalizationCover.adjacent_normalized_cover_connected_genus_five`.
No literal raw-Proj global identification, affine-source open-immersion theorem,
or separate projective-embedding certificate is asserted. No logs, private paths,
historical proof attempts, or custom compiled artifacts are included in this source payload.
