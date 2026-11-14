import json
from fractions import Fraction as Q
from math import gcd, isqrt
from pathlib import Path


directory = Path(__file__).resolve().parent
certificate = json.loads((directory / "HEIGHT_BOUND.json").read_text())
numerator = certificate["primitive_numerator_ascending"]
denominator = certificate["primitive_denominator_ascending"]
degree = certificate["degree"]
common_constant = int(certificate["bezout_common_constant"])

def convolution(first, second):
    result = [0] * (len(first) + len(second) - 1)
    for first_index, first_value in enumerate(first):
        for second_index, second_value in enumerate(second):
            result[first_index + second_index] += first_value * second_value
    return result


norms = [sum(map(abs, numerator)), sum(map(abs, denominator))]
for pair, first, second in zip(certificate["bezout_pairs"], [numerator, numerator[::-1]], [denominator, denominator[::-1]]):
    left = convolution(pair["left"], first)
    right = convolution(pair["right"], second)
    combined = [first_value + second_value for first_value, second_value in zip(left, right)]
    assert combined[0] == common_constant and all(value == 0 for value in combined[1:])
    norms.append(sum(map(abs, pair["left"])) + sum(map(abs, pair["right"])))
assert max(norms) < 2**certificate["height_error_bits"]

def homogeneous_value(values, first, second):
    return sum(value * first**index * second**(degree-index) for index, value in enumerate(values))


first, second = 1, 0
for entry in certificate["orbit"]:
    evaluated = (homogeneous_value(numerator, first, second), homogeneous_value(denominator, first, second))
    divisor = gcd(*evaluated)
    first, second = evaluated[0] // divisor, evaluated[1] // divisor
    bits = max(abs(first), abs(second)).bit_length()
    assert bits == entry["naive_height_bit_length"]
    lower = (Q(bits-1) - Q(certificate["height_error_bits"], degree-1)) / degree**entry["iteration"]
    assert lower == Q(entry["canonical_height_lower"])
assert lower > 0 and Q(certificate["height_error_bits"], 16) / lower < 7

generator = (Q(49), Q(336))
torsion = [None, (Q(0), Q(0)), (Q(81), Q(0)), (Q(121), Q(0))]

def add(first, second):
    if first is None:
        return second
    if second is None:
        return first
    left_x, left_y = first
    right_x, right_y = second
    if left_x == right_x:
        if left_y == -right_y:
            return None
        assert left_y == right_y
        slope = (3*left_x**2 - 404*left_x + 9801)/(2*left_y)
    else:
        slope = (right_y-left_y)/(right_x-left_x)
    result_x = slope**2 + 202-left_x-right_x
    return result_x, -left_y+slope*(left_x-result_x)


def negate(point):
    return None if point is None else (point[0], -point[1])


def multiple(coefficient):
    result = None
    for unused in range(abs(coefficient)):
        result = add(result, generator)
    return negate(result) if coefficient < 0 else result


def source_coordinate(point):
    if point is None or point == negate(generator):
        return None
    if point == generator:
        return Q(-937, 168)
    point_x, point_y = point
    assert point_x != 49
    return (point_y-7*point_x+7)/(2*(point_x-49))


def square_obstruction(integer):
    for prime in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97):
        unit = integer
        valuation = 0
        while unit % prime == 0:
            unit //= prime
            valuation += 1
        if valuation % 2:
            return {"prime": prime, "valuation": valuation, "reason": "odd valuation"}
        if prime == 2 and unit % 8 != 1:
            return {"prime": prime, "valuation": valuation, "unit_mod_8": unit % 8, "reason": "dyadic nonsquare unit"}
        if prime != 2 and pow(unit % prime, (prime-1)//2, prime) == prime-1:
            return {"prime": prime, "valuation": valuation, "unit_mod_prime": unit % prime, "reason": "nonsquare unit"}
    raise AssertionError("No obstruction in the declared finite prime list")


rows = []
for coefficient in range(-4, 5):
    for torsion_index, torsion_point in enumerate(torsion):
        point = add(multiple(coefficient), torsion_point)
        source_z = source_coordinate(point)
        if source_z is None:
            rows.append({"coefficient": coefficient, "torsion_index": torsion_index, "boundary": True})
            continue
        point_x, point_y = point
        assert point_y**2 == point_x**3-202*point_x**2+9801*point_x
        source_pq = (point_x-49)/2-source_z**2-7*source_z-26
        assert source_pq**2 == (source_z**2+50)*(source_z**2+14*source_z+51)
        primitive_first, primitive_second = source_z.numerator, source_z.denominator
        remaining_numerator = (primitive_first**2+50*primitive_second**2)*(primitive_first**2-14*primitive_first*primitive_second+51*primitive_second**2)
        assert isqrt(remaining_numerator)**2 != remaining_numerator
        obstruction = square_obstruction(remaining_numerator)
        rows.append({"coefficient": coefficient, "torsion_index": torsion_index, "z": str(source_z), "boundary": False, "obstruction": obstruction})

assert len(rows) == 36
assert sum(row["boundary"] for row in rows) == 2
assert add((Q(484,9),Q(-8470,27)),torsion[3]) == generator
output = {
    "status": "PASS_INDEPENDENT_INTEGER_BEZOUT_AND_FRACTION_GROUP_CHECKS",
    "height_error_bits": certificate["height_error_bits"],
    "canonical_height_at_infinity_lower": str(lower),
    "product_bound": 6,
    "coefficient_bound": 4,
    "bounded_group_elements": rows,
    "finite_points_surviving": 0,
    "torsion_zero_product_equations": ["z=0", "z^2=-50", "z^2=205/4", "z^2=305/6"],
    "scope": "Complete finite endgame after the height and zero-product arguments. Mordell-Weil completeness is independently supplied by the Magma full-rank and full-index result."
}
(directory / "INDEPENDENT_HEIGHT_POINT_CHECK.json").write_text(json.dumps(output, indent=2)+"\n")
print(output["status"])
print("HEIGHT_ERROR_BITS", certificate["height_error_bits"])
print("HEIGHT_AT_INFINITY_LOWER", lower)
print("NONZERO_PRODUCT_BOUND", 6)
print("FINITE_SURVIVORS", 0)
for coefficient in range(0, 5):
    row = [entry for entry in rows if entry["coefficient"] == coefficient]
    print("ROW",coefficient,["boundary" if entry["boundary"] else entry["obstruction"]["prime"] for entry in row])
