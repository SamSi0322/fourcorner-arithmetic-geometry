import ThetaCoverClassPortable.ThetaLinesContactPoints
import Mathlib.Algebra.Polynomial.RingDivision

namespace FourCorner.ThetaLinesPolynomialContacts
open Polynomial ThetaLinesContactPoints
noncomputable section
variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
attribute [local instance] Classical.propDecidable
local instance infiniteField : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective

 theorem quadratic_factor (a b c x y : k) (hxy : x ≠ y)
    (hx : a*x^2+b*x+c=0) (hy : a*y^2+b*y+c=0) :
    C a*X^2+C b*X+C c=C a*(X-C x)*(X-C y) := by
  have hz : (x-y)*(a*(x+y)+b)=0 := by linear_combination hx-hy
  have hb : b= -a*(x+y) := by
    have hh := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hxy)
    linear_combination hh
  have hc : c=a*x*y := by rw [hb] at hx;linear_combination hx
  rw [hb,hc]
  simp only [map_neg,map_mul,map_add]
  ring

 theorem factored_multiplicity (c x y : k) (hc : c ≠ 0) (hxy : x ≠ y) :
    (C c*(X-C x)^2*(X-C y)^2).rootMultiplicity x=2 ∧
      (C c*(X-C x)^2*(X-C y)^2).rootMultiplicity y=2 := by
  have hn (z : k) : C c*(X-C z)^2 ≠ 0 :=
    mul_ne_zero ((_root_.map_ne_zero C).mpr hc) (pow_ne_zero _ (X_sub_C_ne_zero z))
  constructor
  · rw [mul_right_comm,rootMultiplicity_mul_X_sub_C_pow (hn y)]
    have he : ¬ IsRoot (C c*(X-C y)^2) x := by simp [IsRoot,hc,sub_ne_zero.mpr hxy]
    rw [rootMultiplicity_eq_zero he]
  · rw [rootMultiplicity_mul_X_sub_C_pow (hn x)]
    have he : ¬ IsRoot (C c*(X-C x)^2) y := by simp [IsRoot,hc,sub_ne_zero.mpr (Ne.symm hxy)]
    rw [rootMultiplicity_eq_zero he]

 theorem square_two_double_roots (P : Polynomial k) (c a b d : k)
    (hc : c ≠ 0) (ha : a ≠ 0) (hd : b^2-4*a*d ≠ 0)
    (hp : P=C c*(C a*X^2+C b*X+C d)^2) :
    ∃x y : k,x ≠ y ∧ P=C (c*a^2)*(X-C x)^2*(X-C y)^2 ∧
      P.rootMultiplicity x=2 ∧ P.rootMultiplicity y=2 := by
  obtain ⟨x,y,hxy,hx,hy⟩ := quadratic_affine_roots a b d ha hd
  have hf : P=C (c*a^2)*(X-C x)^2*(X-C y)^2 := by
    rw [hp,quadratic_factor a b d x y hxy hx hy,map_mul,map_pow]
    ring
  exact ⟨x,y,hxy,hf,hf ▸ (factored_multiplicity (c*a^2) x y (mul_ne_zero hc (pow_ne_zero _ ha)) hxy)⟩

/-- The actual univariate restriction of the literal quartic in an affine line chart. -/
def affineRestriction (α β : k) : Polynomial k := thetaF X 1 (C α*X+C β)
def verticalRestriction (t : k) : Polynomial k := thetaF (C t*X) X 1

 theorem affine_square_polynomial (α β c a b d : k)
    (he : ∀x y : k,thetaF x y (α*x+β*y)=c*(a*x^2+b*x*y+d*y^2)^2) :
    affineRestriction α β=C c*(C a*X^2+C b*X+C d)^2 := by
  apply Polynomial.funext
  intro x
  simpa [affineRestriction,thetaF] using he x 1

 theorem vertical_square_polynomial (t c a b d : k)
    (he : ∀x y : k,thetaF (t*x) x y=c*(a*x^2+b*x*y+d*y^2)^2) :
    verticalRestriction t=C c*(C a*X^2+C b*X+C d)^2 := by
  apply Polynomial.funext
  intro x
  simpa [verticalRestriction,thetaF] using he x 1

#print axioms quadratic_factor
#print axioms factored_multiplicity
#print axioms square_two_double_roots
#print axioms affine_square_polynomial
#print axioms vertical_square_polynomial
end
end FourCorner.ThetaLinesPolynomialContacts
