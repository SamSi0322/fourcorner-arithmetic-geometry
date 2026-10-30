import HasseHilbertArithmetic

/-! The actual rational tangent coefficient, its real sign, and its proved
global arithmetic product. Finite local evaluation tables remain separate
mathematical obligations; none is assumed in this file. -/
namespace FourCorner.HasseTangentGlobal

open HasseRationalSource HasseProjectivePoint HasseAnchorChoice
open HasseObstructionArithmetic HasseHilbertArithmetic HilbertWellDefinedHigh11

def firstCoefficient (p : ℚ) : ℚ := -(p-1)
def secondCoefficient (p : ℚ) (P : HomogeneousPoint p) (D : TangentData p P) : ℚ :=
  -p*secondPolar p P.Z P.U P.T P.Z D.w P.T

theorem firstCoefficient_negative (p : ℚ) (hp : 1<p) : firstCoefficient p<0 := by
  dsimp [firstCoefficient]
  linarith

theorem secondCoefficient_negative (p : ℚ) (P : HomogeneousPoint p) (D : TangentData p P) :
    secondCoefficient p P D<0 := D.coefficient_negative

noncomputable def tangentSign (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p)
    (D : TangentData p P) (v : ℕ) : ℤ :=
  rationalSign (firstCoefficient p) (secondCoefficient p P D)
    (ne_of_lt (firstCoefficient_negative p hp)) (ne_of_lt D.coefficient_negative) v

def allSupport (p : ℚ) (P : HomogeneousPoint p) (D : TangentData p P) : Finset ℕ :=
  {0,2} ∪ rationalSupport (firstCoefficient p) ∪ rationalSupport (secondCoefficient p P D)

def oddSupport (p : ℚ) (P : HomogeneousPoint p) (D : TangentData p P) : Finset ℕ :=
  ((allSupport p P D).erase 0).erase 2

/-- The exact real-place entry of the genuine rational tangent symbol is -1. -/
theorem tangentSign_real (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p)
    (D : TangentData p P) : tangentSign p hp P D 0= -1 := by
  rw [tangentSign,rationalSign_real]
  simp only [firstCoefficient_negative p hp,secondCoefficient_negative p P D,and_self,ite_true]

/-- Global reciprocity is applied to the explicitly constructed nonzero
rational coefficients, with all their actual finite support included. -/
theorem tangentSign_global_product (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p)
    (D : TangentData p P) : (∏ v ∈ allSupport p P D,tangentSign p hp P D v)=1 :=
  rational_reciprocity_on_rational_support _ _ _ _

theorem tangentSign_one_outside_support (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p)
    (D : TangentData p P) (v : ℕ) (hv : v ∉ allSupport p P D) :
    tangentSign p hp P D v=1 :=
  rationalSign_one_outside_rational_support _ _ _ _ v hv

/-- This is the unconditional source arithmetic identity the finite-place
table must meet: the product of the dyadic and all odd signs is negative. -/
theorem tangentSign_finite_product (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p)
    (D : TangentData p P) :
    tangentSign p hp P D 2*(∏ q ∈ oddSupport p P D,tangentSign p hp P D q)= -1 := by
  have h0 : 0∈allSupport p P D := by simp [allSupport]
  have h2 : 2∈(allSupport p P D).erase 0 := by simp [allSupport]
  have he := Finset.mul_prod_erase (allSupport p P D) (tangentSign p hp P D) h0
  have he2 := Finset.mul_prod_erase ((allSupport p P D).erase 0) (tangentSign p hp P D) h2
  rw [tangentSign_real p hp P D,tangentSign_global_product p hp P D] at he
  dsimp [oddSupport]
  rw [he2]
  linarith

/-- A genuine rational projective point supplies this entire arithmetic
construction; no affine-domain or anchor witness is a new assumption. -/
theorem projective_source_has_tangent_arithmetic (p : ℚ) (hp : 1<p) (Q : RationalPoint p) :
    ∃ P : HomogeneousPoint p, ∃ D : TangentData p P,
      tangentSign p hp P D 0= -1 ∧
      (∏ v ∈ allSupport p P D,tangentSign p hp P D v)=1 ∧
      tangentSign p hp P D 2*(∏ q ∈ oddSupport p P D,tangentSign p hp P D q)= -1 := by
  let P := toHomogeneousPoint p Q
  let D := tangentData p hp P
  exact ⟨P,D,tangentSign_real p hp P D,tangentSign_global_product p hp P D,
    tangentSign_finite_product p hp P D⟩

#print axioms tangentSign_real
#print axioms tangentSign_global_product
#print axioms tangentSign_one_outside_support
#print axioms tangentSign_finite_product
#print axioms projective_source_has_tangent_arithmetic

end FourCorner.HasseTangentGlobal
