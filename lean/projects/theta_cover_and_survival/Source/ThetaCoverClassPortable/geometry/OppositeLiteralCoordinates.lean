import ThetaCoverClassPortable.geometry.OppositeNormalizedField

noncomputable section
namespace FourCorner.OppositeLiteralCoordinates
open OppositeNormalizedField
variable {K : Type*} [Field K] [CharZero K]

def parameter (mu nu : K) : field mu nu :=
  algebraMap (RatFunc K) (field mu nu) RatFunc.X

def constant (mu nu c : K) : field mu nu :=
  algebraMap (RatFunc K) (field mu nu) (algebraMap K (RatFunc K) c)

def P (mu nu : K) : field mu nu :=
  Multiquadratic.root₁ (RatFunc K) (value mu nu 0) (value mu nu 1) (value mu nu 2)
def Q (mu nu : K) : field mu nu :=
  Multiquadratic.root₂ (RatFunc K) (value mu nu 0) (value mu nu 1) (value mu nu 2)
def R (mu nu : K) : field mu nu :=
  Multiquadratic.root₃ (RatFunc K) (value mu nu 0) (value mu nu 1) (value mu nu 2)

/-- The three selected roots in the constructed degree-eight function field
satisfy all three original affine equations, with their ordered labels. -/
theorem original_equations (mu nu : K) (hA : OppositePolynomials.A mu nu ≠ 0) :
    (parameter mu nu)^2 = (2 * (constant mu nu nu)^2 - (constant mu nu mu)^2) *
      ((P mu nu)^2 - 2 * (constant mu nu nu)^2) ∧
    (Q mu nu)^2 = (P mu nu)^2 + (constant mu nu mu)^2 + 2 * parameter mu nu ∧
    (R mu nu)^2 = (P mu nu)^2 + (constant mu nu mu)^2 - 2 * parameter mu nu := by
  have h0 := congrArg (algebraMap (RatFunc K) (field mu nu)) (value_zero_equation mu nu hA)
  have h1 := congrArg (algebraMap (RatFunc K) (field mu nu)) (value_plus_equation mu nu hA)
  have h2 := congrArg (algebraMap (RatFunc K) (field mu nu)) (value_minus_equation mu nu hA)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [parameter, constant, P, Multiquadratic.root₁_sq, OppositePolynomials.A,
      map_mul, map_sub, map_pow, map_ofNat] using h0.symm
  · simpa only [parameter, constant, P, Q, Multiquadratic.root₁_sq,
      Multiquadratic.root₂_sq, map_add, map_mul, map_pow, map_ofNat] using h1
  · simpa only [parameter, constant, P, R, Multiquadratic.root₁_sq,
      Multiquadratic.root₃_sq, map_add, map_sub, map_mul, map_pow, map_ofNat] using h2

/- The same ordered roots generate the entire field, rather than a smaller
quotient or a disconnected selection of independent square tests. -/
omit [CharZero K] in
theorem coordinates_generate (mu nu : K) :
    IntermediateField.adjoin (RatFunc K) {P mu nu, Q mu nu, R mu nu} = ⊤ :=
  Multiquadratic.roots_generate (RatFunc K) (value mu nu 0) (value mu nu 1) (value mu nu 2)

#print axioms original_equations
#print axioms coordinates_generate
end FourCorner.OppositeLiteralCoordinates
