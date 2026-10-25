import Slot03AdjacentBaseChange
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv

noncomputable section
namespace FourCorner.Slot03Adjacent
open AlgebraicCurve
open scoped TensorProduct
variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

theorem tensor_domain_of_admissible (c : K)
    (h : AdjacentPolynomials.Admissible (algebraMap K L c)) :
    IsDomain (L ⊗[K] AdjacentCoordinateAlgebra.CoordinateRing c) := by
  letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain (algebraMap K L c) h
  exact Function.Injective.isDomain (coordinateEquiv (L := L) c)
    (coordinateEquiv (L := L) c).injective

/-- Genus of the canonical fraction field of the literal scalar-extended quotient. -/
theorem tensor_fraction_genus [IsAlgClosed L] (c : K)
    (h : AdjacentPolynomials.Admissible (algebraMap K L c)) :
    letI := tensor_domain_of_admissible c h
    genusFF L (FractionRing (L ⊗[K] AdjacentCoordinateAlgebra.CoordinateRing c)) = 5 := by
  letI := tensor_domain_of_admissible c h
  letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain (algebraMap K L c) h
  let e : FractionRing (L ⊗[K] AdjacentCoordinateAlgebra.CoordinateRing c) ≃ₐ[L]
      FractionRing (AdjacentCoordinateAlgebra.CoordinateRing (algebraMap K L c)) :=
    IsFractionRing.algEquivOfAlgEquiv (coordinateEquiv (L := L) c)
  let f := AdjacentCoordinateAlgebra.fractionFieldEquiv (algebraMap K L c) h.c_ne_zero h
  exact (genusFF_eq_of_algEquiv (e.trans f)).trans
    (AdjacentCoordinateAlgebra.genusFF_eq_five _ _ h)

theorem rational_tensor_fraction_genus (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    letI := tensor_domain c hc h1 (AlgebraicClosure ℚ)
    genusFF (AlgebraicClosure ℚ)
      (FractionRing ((AlgebraicClosure ℚ) ⊗[ℚ] AdjacentCoordinateAlgebra.CoordinateRing c)) = 5 := by
  exact tensor_fraction_genus c (AdjacentPolynomials.rational_admissible c hc h1)

#print axioms rational_tensor_fraction_genus
#print axioms tensor_domain_of_admissible
#print axioms tensor_fraction_genus
end FourCorner.Slot03Adjacent
