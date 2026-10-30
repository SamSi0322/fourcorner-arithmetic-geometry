import ThetaCoverClassPortable.ThetaRationalRiemannBound
import ThetaCoverClassPortable.SingleOriginPole
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
namespace FourCorner.ThetaRationalPicardInput
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaLiteralModels
attribute [local instance] sourceIntegral sourceSmooth sourceProper constants

/-- Actual Q-rational functions in the native original field, of arbitrarily
large EXACT pole order at OC, regular at EVERY other place. This is proved
from the rational-base Riemann bound, not from Qbar specialization. -/
theorem actual_single_origin_poles (m0 : ℕ) :
    ∃ (f : (C ℚ).functionField) (r : ℕ), f≠0 ∧ m0<r ∧
      originPlace.ord f=-(r:ℤ) ∧
      (∀ v : Place ℚ (C ℚ).functionField, v≠originPlace → 0≤v.ord f) ∧
      Transcendental ℚ f ∧
      FiniteDimensional (IntermediateField.adjoin ℚ ({f} : Set (C ℚ).functionField))
        (C ℚ).functionField := by
  letI := source_isCurveOver
  letI := source_essFiniteType
  obtain ⟨f,r,hf,hr,hord,haway⟩ := SingleOriginPole.exists_single_pole_above
    source_stichtenothGenusExists originPlace originPlace_degree_one m0
  have ht : Transcendental ℚ f := originPlace.transcendental_of_ord_ne_zero (by rw [hord];omega)
  obtain ⟨x,hx,hfd,hsep⟩ := IsCurveOver.exists_separating_transcendental
    (K:=ℚ) (F:=(C ℚ).functionField)
  letI := hfd
  exact ⟨f,r,hf,hr,hord,haway,ht,finiteDimensional_adjoin_of_transcendental x ht⟩

#print axioms actual_single_origin_poles
end FourCorner.ThetaRationalPicardInput
