import json
from pathlib import Path

from sympy import QQ
from sympy.polys.fields import field


base, coordinate = field("coordinate", QQ)
radicand = (coordinate**2+50)*(coordinate**2+14*coordinate+51)

class QuadraticElement:
    def __init__(self, constant, root=0):
        self.constant = base(constant)
        self.root = base(root)

    @staticmethod
    def coerce(value):
        return value if isinstance(value, QuadraticElement) else QuadraticElement(value)

    def __add__(self, other):
        other = self.coerce(other)
        return QuadraticElement(self.constant+other.constant, self.root+other.root)

    __radd__ = __add__

    def __neg__(self):
        return QuadraticElement(-self.constant, -self.root)

    def __sub__(self, other):
        return self+-self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other)+-self

    def __mul__(self, other):
        other = self.coerce(other)
        return QuadraticElement(self.constant*other.constant+self.root*other.root*radicand, self.constant*other.root+self.root*other.constant)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.coerce(other)
        norm = other.constant**2-other.root**2*radicand
        assert norm != 0
        return self*QuadraticElement(other.constant/norm, -other.root/norm)

    def __pow__(self, exponent):
        result = QuadraticElement(1)
        for unused in range(exponent):
            result = result*self
        return result

    def equals(self, other):
        other = self.coerce(other)
        return self.constant == other.constant and self.root == other.root


def verify_curve(point):
    abscissa, ordinate = point
    assert (ordinate**2-abscissa**3+202*abscissa**2-9801*abscissa).equals(0)


def add_points(first, second, double=False):
    left_x, left_y = first
    right_x, right_y = second
    slope = (3*left_x**2-404*left_x+9801)/(2*left_y) if double else (right_y-left_y)/(right_x-left_x)
    result_x = slope**2+202-left_x-right_x
    result = result_x, -left_y+slope*(left_x-result_x)
    verify_curve(result)
    return result


auxiliary = QuadraticElement(coordinate**2+7*coordinate+26, 1)
point = 2*auxiliary+49, (4*coordinate+14)*auxiliary+336
verify_curve(point)
twice = add_points(point,point,double=True)
triple = add_points(twice,point)
shift = QuadraticElement(49), QuadraticElement(336)
shifted = add_points(triple,shift)
image = (shifted[1]-7*shifted[0]+7)/(2*(shifted[0]-49))
certificate = json.loads(Path(__file__).with_name("HEIGHT_BOUND.json").read_text())
numerator = sum(value*coordinate**index for index,value in enumerate(certificate["primitive_numerator_ascending"]))
denominator = sum(value*coordinate**index for index,value in enumerate(certificate["primitive_denominator_ascending"]))
assert image.equals(QuadraticElement(numerator/denominator))
assert ((point[1]-7*point[0]+7)/(2*(point[0]-49))).equals(QuadraticElement(coordinate))
for abscissa, expected in ((0,(-coordinate+700)/(14*coordinate+1)), (81,(-35*coordinate-205)/(4*coordinate+35)), (121,(-35*coordinate-305)/(6*coordinate+35))):
    translated = add_points(point,(QuadraticElement(abscissa),QuadraticElement(0)))
    actual = (translated[1]-7*translated[0]+7)/(2*(translated[0]-49))
    assert actual.equals(QuadraticElement(expected))
print("PASS_INDEPENDENT_FUNCTION_FIELD_TRIPLICATION_AND_ALL_TORSION_TRANSFORMS")
