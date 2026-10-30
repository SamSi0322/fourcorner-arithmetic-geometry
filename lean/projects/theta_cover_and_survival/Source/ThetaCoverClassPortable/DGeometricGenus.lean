import ThetaCoverClassPortable.DBaseChangeGeometry
import ThetaCoverClassPortable.ThetaUniformGeometricGenus
import ThetaCoverClassPortable.ThetaEtaleAllPlaces
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
import Mathlib.Algebra.CharP.Algebra

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
namespace FourCorner.DRationalInputs
namespace Geometric
open ThetaNativeFunctionFieldMap
variable (K : Type) [Field K] [Algebra ℚ K]
abbrev y := Scheme.TwoAffineOpenCover.specMap ℚ K
local instance : IsIntegral (XAt (y K)) := integral_at (y K)
local instance : IsIntegral (coverSource (y K)) := source_integral_at (y K)
local instance : IsProper (cAt (y K)) := proper_at (y K)
local instance : SmoothOfRelativeDimension 1 (cAt (y K)) := smooth_at (y K)
local instance : IsProper (sourceBase (y K)) := source_proper_at (y K)
local instance : SmoothOfRelativeDimension 1 (sourceBase (y K)) := source_smooth_at (y K)
local instance : IsFinite (coverMap (y K)) := cover_finite (y K)
local instance : Etale (coverMap (y K)) := cover_etale (y K)
local instance : Surjective (coverMap (y K)) := cover_surjective (y K)
local instance : Flat (coverMap (y K)) := cover_flat (y K)

abbrev F := (XAt (y K)).functionField
abbrev E := (coverSource (y K)).functionField
abbrev fAlgebra : Algebra K (F K) := (baseToFunctionField (cAt (y K))).toAlgebra
abbrev eAlgebra : Algebra K (E K) := (baseToFunctionField (sourceBase (y K))).toAlgebra
abbrev extensionAlgebra : Algebra (F K) (E K) := (fieldMap (coverMap (y K))).toAlgebra
local instance : Algebra K (F K) := fAlgebra K
local instance : Algebra K (E K) := eAlgebra K
local instance : Algebra (F K) (E K) := extensionAlgebra K

theorem extension_tower : IsScalarTower K (F K) (E K) :=
  IsScalarTower.of_algebraMap_eq fun a =>
    (base_compatibility (coverMap (y K)) (sourceBase (y K)) (cAt (y K)) rfl a).symm
local instance : IsScalarTower K (F K) (E K) := extension_tower K

theorem extension_degree : Module.finrank (F K) (E K) = 2 :=
  ThetaFiniteGenericDegree.degree_two (coverMap (y K)) (cover_rank (y K))

theorem extension_finite : FiniteDimensional (F K) (E K) :=
  Module.finite_of_finrank_pos (by rw [extension_degree K]; decide)
local instance : FiniteDimensional (F K) (E K) := extension_finite K

theorem all_index_one (w : Place K (E K)) : w.ramificationIndex (F K) = 1 :=
  ThetaEtaleAllPlaces.all_index_one (coverMap (y K)) (sourceBase (y K)) (cAt (y K))
    rfl (cover_rank (y K)) w

/-- Here genus five belongs to the ACTUAL source C of the degree-two pi;
it is only an input to Riemann-Hurwitz, never substituted for D's genus. -/
theorem covering_source_genus [IsAlgClosed K] : genusFF K (E K) = 5 := by
  letI := ThetaUniformGeometricGenus.integral_at (y K)
  letI := (baseToFunctionField (pullback.snd (ThetaLiteralModels.cToBase ℚ) (y K))).toAlgebra
  let e := ThetaIsoFunctionField.algEquiv (sourceBase (y K))
    (pullback.snd (ThetaLiteralModels.cToBase ℚ) (y K)) (sourceIso (y K)) (sourceIso_over (y K))
  exact (genusFF_eq_of_algEquiv e).symm.trans (ThetaUniformGeometricGenus.genus_five K)

/-- Uniform genus THREE for the actual native field of D_K, for every
algebraically closed extension K/QQ, by the original etale double cover. -/
theorem genus_three [IsAlgClosed K] : genusFF K (F K) = 3 := by
  letI : IsCurveOver K (F K) :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one (cAt (y K))
      (RingEquiv.refl _) (fun _ => rfl)
  letI : Algebra.EssFiniteType K (F K) := essFiniteType_functionField (cAt (y K))
  letI : IsCurveOver K (E K) :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one (sourceBase (y K))
      (RingEquiv.refl _) (fun _ => rfl)
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  letI : CharZero (F K) := charZero_of_injective_algebraMap (algebraMap K (F K)).injective
  letI : Algebra.IsSeparable (F K) (E K) := inferInstance
  obtain ⟨t,ht,hfd,_⟩ := IsCurveOver.exists_separating_transcendental (K:=K) (F:=F K)
  have htame : ∀ w : Place K (E K), ((w.ramificationIndex (F K) : ℕ) : K) ≠ 0 := by
    intro w
    rw [all_index_one K w]
    simpa only [Nat.cast_one] using (one_ne_zero : (1 : K) ≠ 0)
  have hsum : (∑ᶠ w : Place K (E K), ((w.ramificationIndex (F K) : ℤ)-1)) = 0 := by
    simp [all_index_one K]
  have hRH := two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame ⟨t,ht,hfd⟩ htame
  rw [covering_source_genus K, extension_degree K, hsum] at hRH
  omega
end Geometric

/-- The exact every-field-valued-map genus interface needed for the D
adapter. No external Algebra QQ K or genus hypothesis is added. -/
theorem actual_genus_three {K : Type} [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ Spec (.of ℚ)) :
    letI := integral_at t
    letI := (baseToFunctionField (cAt t)).toAlgebra
    genusFF K (XAt t).functionField = 3 := by
  obtain ⟨a,_⟩ := Spec.map_surjective t
  letI : Algebra ℚ K := a.hom.toAlgebra
  have ht : t = Scheme.TwoAffineOpenCover.specMap ℚ K := ThetaSourceComparison.rational_base_unique _ _
  subst t
  exact Geometric.genus_three K

end FourCorner.DRationalInputs
