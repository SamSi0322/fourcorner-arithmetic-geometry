# Refined critical-prime classification

This project proves `thm:crit-refined` from
*Arithmetic constraints and covering curves for rational distances in a square*.
For every prime p congruent to one modulo four, it proves the equivalence of
excluding 5, 13 and 17; existence of an original signed critical pattern with
nonzero squared doubled product; and infinitely many primitive strict rational
coordinate pairs at every positive depth, with the same four actual p-adic
roots and both required product squares.

The uniform existence proof uses the actual quadratic cover function field,
its proved Hasse bound, complete bad-place bounds and evaluation at one actual
rational place. The signed local construction and converse preserve every
original distance equation, prescribed root sign and exact valuation. The
local-family statements concern actual distinct rational coordinate pairs.

## Reproduce

Keep this directory at `lean/projects/critical_refined` in the full repository.
Use the pinned Lean 4.33.1 toolchain and dependency revisions:

```sh
lake --keep-toolchain --no-cache build CriticalRefinedProject
lake --keep-toolchain env lean --setup .lake/build/ir/RefinedFiniteAudit.setup.json -t0 -Ddebug.skipKernelTC=false Source/RefinedFiniteAudit.lean
```

Lake generates the exact module-provider setup. The package contains 51 owned
source modules and reuses 728 accepted sources through `critical_prime` and
its declared dependencies. Its combined audit checks 13 endpoints; only
`propext`, `Classical.choice` and `Quot.sound` are permitted.

The principal declaration is `FourCorner.CriticalRefinedFull.thm_crit_refined`.
`exclusions_iff_infinite_pairs` and `exclusions_iff_literal_pattern` in the same
namespace record the direct original-coordinate and nonzero-square forms.

Original code is Apache-2.0; dependency headers and notices are retained.
