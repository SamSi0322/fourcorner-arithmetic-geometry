import json
from pathlib import Path

import sympy as sp


u, v = sp.symbols("u v")
denominator = (u + v) * (1 - u * v)
x = v * (1 - u**2) / denominator
y = 2 * u * v / denominator
radius_zero = v * (1 + u**2) / denominator
radius_one = u * (1 + v**2) / denominator
first = sp.expand(v**2 * (1 - u**2)**2 + (denominator - 2 * u * v)**2)
second = sp.expand(u**2 * (1 - v**2)**2 + (denominator - 2 * u * v)**2)

assert sp.cancel(radius_zero**2 - x**2 - y**2) == 0
assert sp.cancel(radius_one**2 - (1 - x)**2 - y**2) == 0
assert sp.cancel(first / denominator**2 - x**2 - (1 - y)**2) == 0
assert sp.cancel(second / denominator**2 - (1 - x)**2 - (1 - y)**2) == 0
assert sp.cancel(y / (radius_zero + x) - u) == 0
assert sp.cancel(y / (radius_one + 1 - x) - v) == 0

first_discriminant = sp.factor(sp.discriminant(first, v))
second_discriminant = sp.factor(sp.discriminant(second, v))
resultant = sp.factor(sp.resultant(first, second, v))
assert first_discriminant == 64 * u**4 * (u - 1)**4 * (u + 1)**4 * (u**2 + 1)**2 * (u**2 + 2*u - 1)**2
assert second_discriminant == 16 * u**4 * (u**2 + 1)**2 * (u**2 + 2*u - 1)**4 * (u**4 + 8*u**3 + 18*u**2 - 8*u + 1)
assert resultant == u**8 * (u**2 + 1)**4 * (5*u**4 + 8*u**3 - 6*u**2 - 8*u + 5)**2
assert sp.expand(u**4 + 8*u**3 + 18*u**2 - 8*u + 1 - (u**2 + 4*u - 1)**2 - 4*u**2) == 0
assert sp.expand(5*u**4 + 8*u**3 - 6*u**2 - 8*u + 5 - 5*(u**2 - 1 + sp.Rational(4, 5)*u)**2 - sp.Rational(4, 5)*u**2) == 0
assert sp.factor(first.subs(v, -u)) == u**2 * (u**2 + 1)**2
assert sp.factor(second.subs(v, -u)) == u**2 * (u**2 + 1)**2

coordinates = sp.symbols("a0 b0 a1 b1 a2 b2")
vectors = [sp.Matrix(coordinates[index:index + 2]) for index in (0, 2, 4)]
norms = [vector.dot(vector) for vector in vectors]
dots = [vectors[0].dot(vectors[1]), vectors[1].dot(vectors[2]), vectors[2].dot(vectors[0])]
cayley_numerator = 4 * (dots[0]**2 * norms[2] + dots[1]**2 * norms[0] + dots[2]**2 * norms[1] - 2 * dots[0] * dots[1] * dots[2] - norms[0] * norms[1] * norms[2])
assert sp.expand(cayley_numerator) == 0

xi, eta, projective_z = sp.symbols("xi eta projective_z")
quartic = 9801*(xi**4 + eta**4) + 19598*xi**2*eta**2 - 39592*(xi**2 + eta**2)*projective_z**2 + 39984*projective_z**4
affine_quartic = quartic.subs(projective_z, 1)
cover_numerator = xi**2 + eta**2 - 2
source_z = (xi**2 - eta**2) / (14 * cover_numerator)
source_pq = 2 * xi / cover_numerator
source_pr = 2 * eta / cover_numerator
source_qr = 2 * xi * eta / cover_numerator

def reduced_on_quartic(expression):
    numerator = sp.cancel(expression).as_numer_denom()[0]
    return sp.rem(numerator, affine_quartic, xi, eta) == 0


assert reduced_on_quartic(source_pq**2 - (source_z**2 + 50)*(source_z**2 + 14*source_z + 51))
assert reduced_on_quartic(source_pr**2 - (source_z**2 + 50)*(source_z**2 - 14*source_z + 51))
assert reduced_on_quartic(source_qr**2 - (source_z**4 - 94*source_z**2 + 2601))
auxiliary = source_pq + source_z**2 + 7*source_z + 26
elliptic_x = 2*auxiliary + 49
elliptic_y = (4*source_z + 14)*auxiliary + 336
assert reduced_on_quartic(elliptic_y**2 - elliptic_x**3 + 202*elliptic_x**2 - 9801*elliptic_x)
e1_x = 49 * source_z**2
e1_y = 343 * source_z * source_qr
assert reduced_on_quartic(e1_y**2 - e1_x**3 + 4606*e1_x**2 - 6245001*e1_x)

prime = 13
projective_points = [(left, right, 1) for left in range(prime) for right in range(prime)]
projective_points += [(left, 1, 0) for left in range(prime)] + [(1, 0, 0)]
quartic_polynomial = sp.Poly(quartic, xi, eta, projective_z)
gradient = [sp.Poly(sp.diff(quartic, variable), xi, eta, projective_z) for variable in (xi, eta, projective_z)]

def evaluate_mod(polynomial, point):
    return sum(int(coefficient) * point[0]**powers[0] * point[1]**powers[1] * point[2]**powers[2] for powers, coefficient in polynomial.terms()) % prime


reduction_points = [point for point in projective_points if evaluate_mod(quartic_polynomial, point) == 0]
assert all(any(evaluate_mod(derivative, point) for derivative in gradient) for point in reduction_points)
principal_matrix = sp.Matrix([[19602, 19598, -39592], [19598, 19602, -39592], [-39592, -39592, 79968]])
principal_minors = []
for mask in range(1, 8):
    positions = [position for position in range(3) if mask & (1 << position)]
    minor = int(principal_matrix.extract(positions, positions).det())
    assert minor % prime != 0
    principal_minors.append(minor)

sign_x = sp.diag(1, -1, -1)
sign_y = sp.diag(-1, 1, -1)
swap_xy = sp.Matrix([[0, -1, 0], [-1, 0, 0], [0, 0, -1]])
correspondences = [sp.eye(3) + 3*involution for involution in (sign_x, sign_y, swap_xy)]
assert all(matrix.trace() == 0 for matrix in correspondences)
assert sp.Matrix.hstack(*(matrix.reshape(9, 1) for matrix in correspondences)).rank() == 3
model_bad_primes = sorted({prime_divisor for minor in principal_minors for prime_divisor in sp.factorint(abs(minor))})

result = {
    "status": "PASS_EXACT_IDENTITIES_AND_BOUNDED_FINITE_FIELD_CHECKS",
    "two_angle_polynomials": {"F": str(first), "G": str(second), "disc_F": str(first_discriminant), "disc_G": str(second_discriminant), "resultant": str(resultant)},
    "cayley_trace_identity": "identically zero for three two-dimensional vectors after clearing norms",
    "quartic_quotient_maps": "PQ, PR, QR and maps to original E4 and E1 identities verified",
    "good_prime": prime,
    "quartic_reduction_points": reduction_points,
    "quartic_reduction_point_count": len(reduction_points),
    "principal_minors": principal_minors,
    "model_bad_prime_candidates": model_bad_primes,
    "three_trace_zero_correspondence_matrices": [matrix.tolist() for matrix in correspondences],
    "scope": "All-parameter polynomial identities and the complete projective reduction over F_13. No rational-point completeness computation or global four-corner exclusion."
}
Path(__file__).with_name("EXACT_TRANSFER_RESULTS.json").write_text(json.dumps(result, indent=2, default=int) + "\n")
print(json.dumps({key: value for key, value in result.items() if key not in {"two_angle_polynomials", "quartic_reduction_points"}}, indent=2, default=int))
