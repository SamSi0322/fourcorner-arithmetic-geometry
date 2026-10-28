import ThetaLocalSurvivalPortable.FreePolynomialPoints
import Mathlib.RingTheory.RingHom.StandardSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal

variable (A K : Type) [CommRing A] [Algebra ℚ A] [Field K] [Algebra ℚ K]

/-- A genuine smooth-relative-dimension-one affine curve has an actual principal
neighborhood of any actual field-valued point, with an actual etale coordinate to A¹. -/
theorem smooth_affine_exists_etale_coordinate
    [SmoothOfRelativeDimension 1 (pointObject A).hom] (φ : A →ₐ[ℚ] K) :
    ∃ r : A, φ r≠0 ∧ ∃ t : MvPolynomial (Fin 1) ℚ →ₐ[ℚ] Localization.Away r,
      t.toRingHom.Etale := by
  have hl : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap ℚ A) :=
    HasRingHomProperty.Spec_iff.mp (inferInstance : SmoothOfRelativeDimension 1 (pointObject A).hom)
  obtain ⟨s,hs,hh⟩ := hl
  have hr : ∃ r∈s,φ r≠0 := by
    by_contra! h
    have hk : Ideal.span s ≤ RingHom.ker φ.toRingHom := Ideal.span_le.mpr h
    rw [hs,top_le_iff] at hk
    exact RingHom.ker_ne_top φ.toRingHom hk
  obtain ⟨r,hrs,hrφ⟩ := hr
  have hstd := hh r hrs
  have hstd' : (algebraMap ℚ (Localization.Away r)).IsStandardSmoothOfRelativeDimension 1 := by
    rw [IsScalarTower.algebraMap_eq ℚ A (Localization.Away r)]
    exact hstd
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Localization.Away r) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hstd'
  obtain ⟨t,ht⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    1 ℚ (Localization.Away r)
  exact ⟨r,hrφ,t,ht⟩

end FourCorner.ThetaLocalSurvival.StrongTopology
