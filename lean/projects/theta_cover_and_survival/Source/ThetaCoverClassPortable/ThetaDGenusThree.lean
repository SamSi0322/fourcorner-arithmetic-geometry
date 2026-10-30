import ThetaCoverClassPortable.ThetaEtaleAllPlaces
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame

namespace FourCorner.ThetaDGenusThree
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDActualFieldCover
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsIntegral coverSource := cover_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : IsProper sourceBase := source_proper
local instance : SmoothOfRelativeDimension 1 sourceBase := source_smooth
local instance : IsFinite coverMap := cover_finite
local instance : Etale coverMap := cover_etale
local instance : Surjective coverMap := cover_surjective
local instance : Algebra K F := fAlgebra
local instance : Algebra K E := eAlgebra
local instance : Algebra F E := extensionAlgebra
local instance : IsScalarTower K F E := extension_tower
local instance : FiniteDimensional F E := extension_finite

/-- EVERY native place, including every point over every original chart
and infinity, is genuinely unramified in the actual covering extension. -/
theorem all_index_one (w : Place K E) : w.ramificationIndex F=1 :=
  ThetaEtaleAllPlaces.all_index_one coverMap sourceBase toBase rfl cover_rank w

/-- Actual genus THREE of the native function field of the actual Qbar
pullback of the original smooth plane quartic. Derived from genus-five C,
actual degree-two extension and all-place unramifiedness; no genus input. -/
theorem genus_three : genusFF K F=3 := by
  letI : IsCurveOver K F := field_isCurveOver
  letI : Algebra.EssFiniteType K F := field_essFiniteType
  letI : IsCurveOver K E := isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    sourceBase (RingEquiv.refl _) (fun _ => rfl)
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  letI : Algebra.IsSeparable F E := inferInstance
  obtain ⟨t,ht,hfd,_⟩ := IsCurveOver.exists_separating_transcendental (K:=K) (F:=F)
  have htame : ∀w : Place K E,((w.ramificationIndex F : ℕ) : K) ≠ 0 := by
    intro w
    rw [all_index_one]
    exact one_ne_zero
  have hsum : (∑ᶠw : Place K E,((w.ramificationIndex F : ℤ)-1))=0 := by simp [all_index_one]
  have hRH := two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame ⟨t,ht,hfd⟩ htame
  rw [source_genus,extension_degree,hsum] at hRH
  omega

#print axioms all_index_one
#print axioms genus_three
end
end FourCorner.ThetaDGenusThree
