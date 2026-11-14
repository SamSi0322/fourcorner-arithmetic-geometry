# Exact arithmetic certificates

These checks accompany the written proofs. They are finite identity and
certificate verifications, rather than a search over the parameters of
the unrestricted four-corner problem.

## Symmetric models and quotient maps

With Python 3 and SymPy 1.14.0:

```sh
python3 models/verify_identities.py
```

This checks the four same-point return identities, the normalization,
the source square identities, the plane-quartic conic and quotient maps,
the explicit elliptic isogeny, and the signed-sum product identities.
It does not replace the written genus, valuation or independence proofs.

## The opposite-distance difference 1/5

From `one_fifth/` run:

```sh
python3 verify_transfer.py
python3 verify_triplication_function.py
python3 verify_height_and_points.py
magma -b mordell_weil_certificate.m
```

The first three checks use exact symbolic or rational/integer arithmetic.
The last uses the rational two-Selmer group and full saturation in Magma
2.29-7. It uses neither an analytic rank calculation nor a GRH option.
The height bound proves that the displayed finite endgame is exhaustive.
The JSON data and the Magma transcript are included for reproduction.
