# Arithmetic constraints and covering curves for rational distances in a square

Yuan Si — postpublication Lean development

This archive accompanies the mathematical preprint. It contains the PDF and
self-contained LaTeX sources, a partial Lean formalization, pinned dependencies,
reproduction instructions, a statement-level coverage table and source hashes.

The current Lean development fully verifies 48 of the 69 numbered statements. Further
formalization is ongoing. The exact coverage is recorded in `lean/coverage.csv`.
The arithmetic and geometric results of the paper are stated and proved in the
manuscript; the original global square rational-distance problem remains open.

- `paper/`: PDF and LaTeX sources, CC BY 4.0.
- `lean/`: checked Lean source projects and coverage, Apache-2.0 for original code.
- `LICENSES/`: license notices; vendor directories retain upstream licenses.
- `SHA256SUMS`: release file checksums.

Development will continue on GitHub, with verified source snapshots archived
as subsequent Zenodo versions. Cite the DOI of the specific version used.

The published [v1.0.0 Zenodo archive](https://doi.org/10.5281/zenodo.23638745)
remains at 34 of 69 statements. This development branch adds the complete
Hasse-family norm lemma and the two complete fixed-distance genus-five
propositions. The paper itself is unchanged.

Development also includes the complete common-curve genus/boundary theorem,
residue-matrix exclusion and explicit infinite family, with full source-point
and regular-section identities.

The genus-seventeen companion proves the complete finite twist construction,
unramified double covers of the same genus-nine curve, and rational-point
lifting that preserves the original point and all five ordered coordinates.

The common-source companion also proves the odd-prime row lemma for both
permitted whole-subgroup reduction probes, retaining every source compensator.

The complete common-source character criterion is also formalized, including
the original logarithmic character and the equivalent finite certificate.

The finite-local companion proves that the stated finite tests give exactly the
everywhere-local twist set, including the real place, and proves the resulting
rational-point exclusion implication.

The critical-elliptic companion proves the original curve's smoothness, geometric
connectedness, elliptic isomorphism over its base field, and complete eight-point
boundary classification after every extension of constants.

The critical-prime companion proves the exact exceptional-prime classification
and infinitely many simultaneous local realizations, for arbitrary finite prime
sets and prescribed depths, using the original ordered distance equations.

The original-cover companion identifies the independently constructed ordered
source function field with the original four-distance surface field adjoined
with the specified square root, and proves that the extension has degree two.
