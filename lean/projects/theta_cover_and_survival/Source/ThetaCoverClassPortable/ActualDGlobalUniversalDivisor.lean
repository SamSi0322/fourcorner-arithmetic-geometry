import ThetaCoverClassPortable.DCurveAffineNeighborhoods
import ThetaCoverClassPortable.GlobalUniversalDivisor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_isProper

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FourCorner.DRationalInputs

/-- The actual original D after an arbitrary Q-scheme base change has a
genuine GLOBAL universal degree-d divisor with all-Scheme classification. -/
theorem actual_baseChange_exists_isUniversal {B : Scheme}
    (qB : B ⟶ Spec (.of ℚ)) (d : ℕ) :
    ∃ (Y : Scheme) (y : Y ⟶ B)
      (Duniv : RelEffCartierDiv (pullback.snd toBase qB) d y), Duniv.IsUniversal := by
  letI : IsProper toBase := proper
  letI : SmoothOfRelativeDimension 1 toBase := smooth
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  apply FourCorner.GlobalUniversalDivisor.exists_isUniversal qB (pullback.snd _ _)
  intro V F hF
  exact DCurveAffineNeighborhoods.relative_affine_basechange qB V.1 V.2 F hF

/-- On every Noetherian Q-algebra, the same actual D divisor parameter
space is proper. No Picard space or representation is assumed. -/
theorem actual_ringBase_proper_universal_divisor
    (A : Type) [CommRing A] [Algebra ℚ A] [IsNoetherianRing A] (d : ℕ) :
    ∃ (Y : Scheme) (y : Y ⟶ Spec (.of A))
      (Duniv : RelEffCartierDiv (SmoothProperCurve.baseChange ℚ toBase A) d y),
      Duniv.IsUniversal ∧ IsProper y := by
  letI : IsProper toBase := proper
  letI : SmoothOfRelativeDimension 1 toBase := smooth
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  obtain ⟨Y,y,D,hD⟩ := actual_baseChange_exists_isUniversal (SmoothProperCurve.specMap ℚ A) d
  exact ⟨Y,y,D,hD,hD.isProper⟩

#print axioms actual_baseChange_exists_isUniversal
#print axioms actual_ringBase_proper_universal_divisor
end FourCorner.DRationalInputs
