# Common finite places

This source project proves the full `prop:common-finite-places`, using the exact
finite exceptional set and exact twist set on the actual native curves. Outside
the exceptional primes, a genuine rational place of the literal finite-field
five-root field yields ordered finite/branch/infinity residues. Explicit Hensel
and transcendental-parameter constructions produce a field embedding and an
actual Qp-valued point of the same canonical curve. The full theorem identifies
the finite tests with everywhere local solubility, and their failure excludes
rational points of the original D_t.

The verification entry retains true finite-base genus seventeen, independently
proved full constants, the actual degree-one place/Hasse--Weil bound, and complete
same-place seven-chart data with original P,C,M,B coordinates. Zero and infinity
are included. No good model, assigned genus, rational-place or local-point
hypothesis replaces the conclusion.

Install as `lean/projects/common_finite_places` in the accompanying source tree.
The direct source dependency is sibling `common_genus17`; its existing parents
supply 551 shared proof sources, without copies. This payload adds 209 exact
missing source modules and one verification entry. All mathematical source bytes
are unchanged from the frozen checks. The 144 Hasse replay modules include 141
Apache-2.0 upstream sources; reversing only the recorded import replacements
recovers every byte at the pinned upstream revision. Source provenance and
individual required parent hashes are declarative JSON records.

Use Lean 4.33.1 and the pinned local dependencies, then run:

    LEAN_NUM_THREADS=1 lake --keep-toolchain --no-cache build
    lake --keep-toolchain --no-cache env lean -t0 -Ddebug.skipKernelTC=false --setup .lake/build/ir/FiniteLocalPackage.setup.json -R Source Source/FiniteLocalPackage.lean

Run the build first so Lake generates the relative setup file used by cold
checking. Its import map identifies the exact provider for nested modules split
between this project and its parents; a raw standalone command omits that map.
Generated setup files and absolute host paths are build evidence, not source
payload files.

The main declaration is `FourCorner.LocalPointCompatibility.common_finite_places`.
Only propext, Classical.choice and Quot.sound are permitted in the audited axiom
lists. Explicit exact-module Lake ownership avoids claiming parent namespaces.
No compiled artifacts, private paths, prompts or logs are included in this
source-only payload. Nine standard git dependencies retain their exact pins.
