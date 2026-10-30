# Uniform arithmetic obstruction for the Hasse family

This project proves `thm:hp-uniform` from
*Arithmetic constraints and covering curves for rational distances in a square*.
It retains the original rational parameter domain, everywhere-local condition
and arithmetic obstruction bit. When that bit is one, the original projective
three-quadric curve has no rational point.

The proof constructs one rational tangent coefficient from each hypothetical
source point, proves its global sign relation from quadratic reciprocity,
and computes every odd and dyadic contribution. All valuation depths,
denominators and the full projective boundary are retained. The final theorem
also has an explicit homogeneous-coordinate wrapper that assumes none of the
coordinates nonzero individually.

## Reproduce

Keep this directory at `lean/projects/hasse_uniform` in the full repository.
Use the pinned Lean 4.33.1 toolchain and dependency revisions:

```sh
lake --keep-toolchain --no-cache build HasseUniformProject
lake --keep-toolchain env lean --setup .lake/build/ir/HasseUniformCompleteAudit.setup.json -t0 -Ddebug.skipKernelTC=false Source/HasseUniformCompleteAudit.lean
```

Lake generates the exact module-provider setup during the build. The package
contains 68 owned source modules and reuses 27 accepted sources from the main
companion. Its combined audit checks 14 endpoints; only `propext`,
`Classical.choice` and `Quot.sound` are permitted.

The principal declarations are `FourCorner.HasseUniformNoPoint.hp_uniform`,
`hp_uniform_literal`, `hp_uniform_four_squares`, and `obstruction_zero` in the
same namespace. This is a complete direct arithmetic proof of the numbered
no-point theorem. The manuscript's geometric Brauer and Picard construction
is a separate argument and is not a dependency of this formal proof.

Original code is Apache-2.0; dependencies retain their original notices.
