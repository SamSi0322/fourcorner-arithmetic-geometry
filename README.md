# Arithmetic constraints and covering curves for rational distances in a square

Yuan Si — version 1.1.0

This release contains the English mathematical preprint, its self-contained
LaTeX sources, a partial Lean companion, and exact arithmetic certificates.

The manuscript adds normalized symmetric return maps, genus-three pencils
with explicit elliptic factors, a dyadic independence criterion for the
actual elliptic sources, exact valuations of signed distance sums, and
denominator-pattern restrictions. It also determines every rational point
of the genus-three quotient for opposite-distance difference 1/5 and of
its genus-five double cover, excluding that entire source at every height.
The unrestricted square rational-distance problem remains open.

The paper now has **83 numbered mathematical statements**. The Lean
companion fully formalizes **59**, all among the original 69 statements.
The remaining 10 original statements and 14 added statements have written
proofs in the paper and are not yet fully formalized. Exact coverage and
the permitted axioms are listed in `lean/coverage.csv` and
`lean/coverage.json`. The published version 1.0.0 contains 34/69.

- `paper/`: manuscript PDF and complete LaTeX sources, CC BY 4.0.
- `lean/`: checked source projects, pinned dependencies and a reproducible
  build/axiom verifier. Original code is Apache-2.0.
- `certificates/`: exact symbolic checks and the one-fifth arithmetic
  certificates, also Apache-2.0 for the original code.
- `LICENSES/`: licenses; third-party files retain their original notices.
- `CHANGELOG.md`: mathematical and formalization changes since version 1.0.0.
- `SHA256SUMS`: release file hashes.

Development: <https://github.com/SamSi0322/fourcorner-arithmetic-geometry>.
This version: <https://doi.org/10.5281/zenodo.24212887>.
All versions: <https://doi.org/10.5281/zenodo.23638744>.
Cite the DOI of the specific archived version used.
