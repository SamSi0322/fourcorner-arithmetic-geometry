# Critical elliptic curve formalization

This project proves the complete proposition `prop:crit-elliptic` from
*Arithmetic constraints and covering curves for rational distances in a square*.
For every field of characteristic different from two and every iota with
`iota^2 = -1`, it proves smoothness and geometric connectedness of the literal
intersection of two quadrics, its isomorphism over the original field with an
independent smooth projective completion of `y^2 = x^3 - x`, and the complete
eight-point boundary classification over every extension field.

The proof retains the actual homogeneous coordinate ring, all affine charts,
the original scalar maps, the native generic stalks and exact Scheme-point
identities. The direct function-field isomorphism is extended by the valuative
criterion. The eight points remain distinct after every field extension.

## Build and verify

Keep this directory at `lean/projects/critical_elliptic`, beside the declared
`opposite_genus` dependency and the rest of this repository's Lean source tree.
Use the pinned Lean 4.33.1 toolchain and dependency revisions:

```sh
lake --keep-toolchain --no-cache build CriticalEllipticProject
lake --keep-toolchain env lean --setup .lake/build/ir/CriticalEllipticPackage.setup.json -t0 -Ddebug.skipKernelTC=false Source/CriticalEllipticPackage.lean
```

Lake generates the module-provider setup during the build. Generated setup
files, compiled artifacts and machine-specific paths are not distributed.
The source package has 67 owned files and reuses 401 exact parent source files.
The complete audit checks 84 declaration endpoints. Their permitted axiom
closures are `propext`, `Classical.choice` and `Quot.sound`.

The main declaration is `FourCorner.CriticalEllipticFull.critical_elliptic`.
The manuscript coverage table records this project's scope within the complete
69-statement formalization programme. Licenses and upstream attribution are
retained in `LICENSE`, `NOTICE` and `UPSTREAM_DERIVATION.json`.
