# Infinite Hasse-failure family

This package formalizes the complete explicit infinite family of genus-five
curves in Theorem `thm:hp-infinite`. For every nonnegative integer index, it
uses the original three-quadric projective curve and the paper’s exact rational
parameter. It proves smoothness, geometric genus five, points at every completion
of the rationals, a point in the strict real distance region, and absence of
rational points. The family contains infinitely many unmarked geometric
isomorphism classes.

The proof preserves the literal projective model through its actual scheme and
function-field identifications. The geometric infinitude follows by deriving
branch-set equivalence from arbitrary unmarked curve isomorphisms. Local points
are constructed at every valuation depth and on every required chart. A finite
residue certificate handles the fixed small primes; a uniform curve argument
handles all larger primes.

The 82 source modules reuse the accepted `common_finite_places`, `hasse_uniform`
and `theta_quotient` projects. Lean 4.33.1 and all dependency revisions are pinned
in the supplied toolchain and manifest. Run the repository’s `lean/verify.py`
for the complete project build and cold-kernel endpoint audit. This package’s
build target is `HasseInfiniteProject` and its audit is
`Source/HpInfiniteCompleteAudit.lean`.

Author: Yuan Si. Original code: Apache-2.0. Dependency licences are retained.
