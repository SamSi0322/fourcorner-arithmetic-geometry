# Critical-prime classification and simultaneous local realization

This project proves `thm:crit-basic` and `cor:crit-crt` from
*Arithmetic constraints and covering curves for rational distances in a square*.
For primes congruent to one modulo four, it proves the complete classification
with exceptions 5 and 13, including the equivalence with infinitely many strict
primitive integer triples at every positive local depth. It also proves the
simultaneous construction for arbitrary finite prime sets and prescribed depths.
The constructed roots belong to each specified completed field Q_p and satisfy
all four original ordered distance equations at the same coordinate triple.

The existence argument derives the actual full constant field, finite-base
genus one and Hasse–Weil bound, removes the entire bad-place set of cardinality
at most 24, and evaluates the original ordered functions at one actual rational
place. The converse normalizes the given four p-adic roots at every depth.
Both infinite integer triples and infinite distinct rational coordinate pairs
are proved. The exceptional content conclusion preserves the original rational
point and all four radii in its least-denominator primitive model.

## Build and verify

Keep this directory at `lean/projects/critical_prime` in the full repository,
beside its declared accepted source dependencies. Use the pinned Lean 4.33.1
compiler and the revisions in `lake-manifest.json`:

```sh
lake --keep-toolchain --no-cache build CriticalPrimeProject
lake --keep-toolchain env lean --setup .lake/build/ir/CriticalPrimeFullAudit.setup.json -t0 -Ddebug.skipKernelTC=false Source/CriticalPrimeFullAudit.lean
```

Lake generates the exact module-provider setup during the build. The source
package contains 37 owned modules and reuses 664 parent modules. Its complete
audit has 46 declared endpoints; only `propext`, `Classical.choice` and
`Quot.sound` are permitted. Sources and import-only path renames are recorded
in the package manifests. Compiled artifacts and generated setup files are
not distributed.

The main declarations are `FourCorner.critical_basic`,
`FourCorner.critical_basic_original_source` and `FourCorner.critical_crt`.
The repository coverage table records their scope in the 69-statement programme.
