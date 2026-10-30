# The explicit genus-five quotient curve

This project proves `prop:theta-quotient` from
*Arithmetic constraints and covering curves for rational distances in a square*.
It uses the original projective three-quadric curve C and the original plane
quartic D, with the displayed projection and sign-change involution.

The proof establishes smoothness, geometric connectedness and genus five of C,
classifies its complete eight-point rational boundary at T=0, and identifies
the two original marked points. The original projection is finite étale,
surjective and of rank two at every target point. Its involution has no fixed
field-valued point. The quotient is verified through the full invariant
algebras and the actual identity/involution kernel-pair diagrams on every
target chart. All original maps and coordinate labels are retained.

## Reproduce

Keep this directory at `lean/projects/theta_quotient` in the full repository.
Use the pinned Lean 4.33.1 toolchain and dependency revisions:

```sh
lake --keep-toolchain --no-cache build ThetaQuotientProject
lake --keep-toolchain env lean --setup .lake/build/ir/ThetaQuotientAudit.setup.json -t0 -Ddebug.skipKernelTC=false Source/ThetaQuotientAudit.lean
```

Lake generates the exact module-provider setup. This package contains 48 owned
source modules and reuses 460 accepted sources through `critical_elliptic` and
its `opposite_genus` dependency. Its combined audit checks 18 endpoints; only
`propext`, `Classical.choice` and `Quot.sound` are permitted.

The principal declaration is `FourCorner.ThetaQuotient.prop_theta_quotient`.
The geometric genus refers to the actual categorical base change to the
algebraic closure of Q. The quotient certificate specifies all original
charts, invariant maps, universal properties and graph equations.

Original code is Apache-2.0. Adapted Mathlib sources retain their copyright
and license notices; dependency notices are preserved.
