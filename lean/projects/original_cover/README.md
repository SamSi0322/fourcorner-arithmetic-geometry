# The original ordered-source quadratic cover

This project proves `prop:ell-original-cover` from
*Arithmetic constraints and covering curves for rational distances in a square*.
For every nonzero rational parameter n, it identifies the independently
constructed ordered five-root function field with the original four-distance
surface field adjoined with q, where

    q^2 = ((r0*r3 + r1*r2)^2 - 1) / n.

The extension has actual vector-space degree two. The field embedding preserves
both position coordinates and all four ordered radii. Neither field is defined
by the asserted comparison: the original field comes from the literal
four-square coordinate quotient, and the ordered source is built separately
from its five specified radicals. Dominance, injectivity, generation, and
nonsquareness are proved.

## Reproduce

Keep this directory at `lean/projects/original_cover` in the full repository.
Use the pinned Lean 4.33.1 toolchain and dependency revisions:

```sh
lake --keep-toolchain --no-cache build OriginalCoverProject
lake --keep-toolchain env lean --setup .lake/build/ir/OriginalCoverAudit.setup.json -t0 -Ddebug.skipKernelTC=false Source/OriginalCoverAudit.lean
```

Lake generates the module-provider setup during the build. The package has
18 owned source modules and reuses seven accepted source modules through its
declared dependencies. Its combined audit checks ten endpoints. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted.

The main declaration is
`FourCorner.OriginalCoverCompletion.OrderedSource.prop_ell_original_cover`.
This package proves the stated function-field proposition. It does not add a
rational-point exclusion or a global solution of the square-distance problem.
Original code is licensed under Apache-2.0; dependencies retain their notices.
