# The complete 15569 source exclusion

This project proves `thm:cs-15569` and `cor:cs-15569-layer` from
*Arithmetic constraints and covering curves for rational distances in a square*.
It excludes every original ordered rational elliptic source at n=15569 whose
same return value is square over Q_2, Q_3 and Q_113. The corollary applies to
every original strict rational-distance point and its canonical squarefree
kernel of `(r0*r3 + r1*r2)^2 - 1`.

The proof constructs the full rational subgroup decomposition, proves the
complete Kummer and compensation statements, and uses exact local characters
and actual finite-field reduction maps. It supplies these facts internally;
no rank, basis, saturation, chosen residue image or height bound is an input
to either manuscript theorem. Both the two ordered source slots and all four
original radii in the layer corollary are retained.

## Reproduce

Keep this directory at `lean/projects/cs15569` in the full repository.
Use the pinned Lean 4.33.1 toolchain and dependency revisions:

```sh
lake --keep-toolchain --no-cache build Cs15569Project
lake --keep-toolchain env lean --setup .lake/build/ir/Cs15569Audit.setup.json -t0 -Ddebug.skipKernelTC=false Source/Cs15569Audit.lean
```

Lake generates the exact module-provider setup. The package contains 64 source
modules, including 38 unchanged source copies from earlier verified companions,
and reuses 59 root and elliptic-foundation sources through declared dependencies.
Two support-module paths have import-only aliases to keep Lake ownership
unambiguous; mathematical namespaces and proof bodies are unchanged. The source,
ownership and import manifests record these details.

The combined audit checks 26 endpoints. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. The principal declarations in namespace
`FourCorner.Cs15569Completion` are `cs15569_source_exclusion`,
`cs15569_source_exclusion_cast` and `cs15569_layer`.

Original code is Apache-2.0. Existing source headers and upstream dependency
license notices are retained.
