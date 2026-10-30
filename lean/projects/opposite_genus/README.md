# Opposite-pair genus-five proof

This source package proves `FourCorner.OppositeProjective.ExactGenus.prop_ell_opposite_genus` for every rational `mu/nu` with `nu ≠ 0` and `0 < mu/nu < 2`.

The theorem concerns the actual three-quadric projective intersection in P4. It includes its closed immersion, compatibility with the rational base map, integrality, properness, smoothness of relative dimension one, geometric connectedness, and finite global relative Kähler differentials of dimension five on its actual categorical Q̄ pullback. The literal projective function field is constructed from the original radical coordinate ring. No model isomorphism or genus is assumed.

The entry point is `Source/OppositeGenus.lean`; the main proof is `Source/OppositeProjectiveGenusFive.lean`. `SOURCE_MANIFEST.json` identifies every nonstandard source, its exact hash, its compile options, and its license provenance. It includes only the transitive source closure needed by this target.

## Pinned build

- Lean: `leanprover/lean4:v4.33.1`
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`
- Other standard dependencies: exact revisions in `lake-manifest.json`

The declarative `lakefile.lean` assigns each module its original compile options. With the pinned dependencies available, run:

```sh
lake --no-cache build
```

Mathlib's upstream metadata at this revision names Lean 4.33.0. Its public 4.33.0 binary cache is incompatible with this package's 4.33.1 toolchain. Keep the pinned root toolchain; compile the necessary standard dependency sources with 4.33.1 or reuse an independently verified compatible 4.33.1 cache. Do not relabel 4.33.0 artifacts.

## Isolated source replay with a compatible standard cache

`rebuild.py` provides a separate reproducibility check. It accepts only standard dependency namespaces in the supplied cache, removes all pre-existing packaged nonstandard objects, rebuilds every packaged source, and cold-checks the main proof and entry point. It performs no downloads or external service calls.

```sh
python3 rebuild.py \
  --lean /path/to/lean-4.33.1 \
  --standard-cache /path/to/compatible-standard-cache \
  --evidence-out /path/outside/this/source-package \
  --jobs 2
```

The cache must contain the standard `.olean` and matching interpreter `.ir` artifacts built from the locked dependencies with Lean 4.33.1. It must contain no prior project proof modules. This cache is not included in the source payload.

A successful replay produces `FULL_REBUILD_ACCEPTANCE.json` and separate per-module receipts in the chosen evidence directory. Final cold checks use `-t0 -Ddebug.skipKernelTC=false`; the permitted transitive axiom list is `propext`, `Classical.choice`, and `Quot.sound`.

## Licensing

Original project proofs and integration support are licensed under Apache-2.0. Adapted upstream sources from `anthropics/fermats-last-theorem`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, retain their Apache-2.0 provenance and original notices. See `LICENSE`, `NOTICE`, and `SOURCE_MANIFEST.json`. Lean, Mathlib, and their standard dependencies are not vendored and retain their own licenses. The manuscript is not included in this code package.
