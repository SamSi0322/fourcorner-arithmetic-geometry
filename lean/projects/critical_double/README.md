# The normalized critical product-square double cover

This project proves `prop:crit-double` from
*Arithmetic constraints and covering curves for rational distances in a square*.
The original critical curve and the same primitive extension obtained by
adjoining the stated product square root are retained on every chart.

The original cover map is proved finite etale of degree two between smooth,
proper, geometrically connected genus-one curves with rational points. Over
each specified finite field, the proof counts actual scheme points above the
literal boundary, obtains the exact 16/8 count and character-count formula,
and proves projective rescaling invariance. Point/place comparisons preserve
the fixed field maps, the image under the original cover map, and the actual
coordinates of the same point, including all poles and normalized boundary
branches.

## Reproduce

Keep this directory at `lean/projects/critical_double` in the full repository.
Use the pinned Lean 4.33.1 toolchain and dependency revisions:

```sh
lake --keep-toolchain --no-cache build CriticalDoubleProject
lake --keep-toolchain env lean --setup .lake/build/ir/CriticalDoubleFullAudit.setup.json -t0 -Ddebug.skipKernelTC=false Source/CriticalDoubleFullAudit.lean
```

Lake generates the exact module-provider setup. The package contains 55 owned
source modules and reuses 753 accepted sources through `critical_refined` and
its declared dependencies. Its combined audit checks 22 endpoints; only
`propext`, `Classical.choice` and `Quot.sound` are permitted.

The main declaration is `FourCorner.CriticalDoubleFull.prop_crit_double`;
`finite_statement` in the same namespace gives the complete finite-field
specialization. Geometric genus is expressed using the actual native function
fields after every algebraically closed extension of constants.

Original code is Apache-2.0; upstream source headers and notices are retained.
