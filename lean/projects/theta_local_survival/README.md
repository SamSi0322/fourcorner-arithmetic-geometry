# Theta local survival

This package formalizes the theorem named
`FourCorner.ThetaLocalSurvival.StrongTopology.theta_local_survival`.
It contains the complete custom source dependency cone, including the genuine
multiplication, geometric-component descent, local-field topology and real
covering arguments. The original mathematical declaration names and proof
bodies are preserved. Custom module names have the unique prefix
`ThetaLocalSurvivalPortable`; `MODULE_MAPPING.json` records this import-only
change.

The theorem uses an actual proper smooth relative curve over QQ, an actual
proper geometrically integral group scheme, actual rational and geometric
points, and the canonical strong topology on field-valued scheme points.
The proper-curve statement includes the projective-curve case. Inspect the
kernel-printed theorem in the audit output for the exact quantified statement.

Install Lean `v4.33.1` through elan, then run:

```
python3 verify.py
```

The package requires Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. Lake obtains the exact dependency
revisions recorded in `lake-manifest.json`. No private source or binary path
is required. Verification builds the package, replays every custom proof
source in ordinary and trust-zero modes, checks that both replay outputs equal the actual Lake-produced object, pins the complete implicit toolchain artifact baseline before and after the batch, and
runs the full standard-axiom and unsafe-dependency audit. Evidence is written
under a fresh `verification/` directory.

This is the complete formalization of the paper theorem `thm:theta-local-survival`.
The coordinate paths and Jacobian-specific corollaries are separate statements.
The ordinary and trust-zero checks agree with every Lake-produced custom object;
the complete dependency audit uses only the standard three axioms.
