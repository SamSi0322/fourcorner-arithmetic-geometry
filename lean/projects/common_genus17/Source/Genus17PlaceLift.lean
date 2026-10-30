import Genus17Support
import RationalPlaceSourceAnyAlgebra
import Genus17PowerBasis
import QuadraticPlaceExtension

noncomputable section
open AlgebraicCurve
namespace FourCorner.Genus17PlaceLift
open Genus17Geometry CommonRationalPlace CommonPostGeometricGenus
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual rational place of the original four-root field extends to a
rational place of ONE literal fifth-root field with kappa in the exact K_t. -/
theorem rational_place_lifts (t : ℚ) (ht : 1 < t) :
    letI := CommonPostGeometricGenus.modelFieldAlgebra t
    ∀ (w : Place ℚ (baseField t)) (hw : w.IsRational),
    ∃ κ ∈ Genus17Support.twists t, 0 < κ ∧
      letI := Genus17Geometry.modelFieldAlgebra t κ
      ∃ v : Place ℚ (field t κ), v.restrict (baseField t) = w ∧
        ∃ hv : v.IsRational, ∃ u : ℚ, 0 < u ∧
          ∃ z : v.toValuationSubring, (z : field t κ) = fifthRoot t κ ∧ rationalEval v hv z = u := by
  letI := CommonPostGeometricGenus.modelFieldAlgebra t
  intro w hw
  let S := RationalPlaceSourceAnyAlgebra.literalSource t ht
    (CommonPostGeometricGenus.modelFieldAlgebra t) w hw
  obtain ⟨κ,hκ,hκpos,u,hupos,hell,hu⟩ := Genus17Support.source_has_global_twist ht S
  refine ⟨κ,hκ,hκpos,?_⟩
  letI := Genus17Geometry.modelFieldAlgebra t κ
  let A := w.toValuationSubring
  let F := baseField t
  let E := field t κ
  obtain ⟨e,he,hve⟩ := RationalPlaceSourceAnyAlgebra.coordinates t ht
    (CommonPostGeometricGenus.modelFieldAlgebra t) w hw 0
  have he' : (e : F) = CommonLiteralField.ell ℚ t := by
    simpa only [CommonPointSource.orderedFunction,Matrix.cons_val_zero] using he
  have hve' : rationalEval w hw e = S.ell := by
    simpa only [CommonPointSource.orderedValue,Matrix.cons_val_zero] using hve
  let a : A := e * algebraMap ℚ A κ⁻¹
  have haF : (a : F) = CommonGenus17Field.radicand ℚ t κ := by
    change (e : F) * algebraMap ℚ F κ⁻¹ = _
    rw [he']
    simp only [CommonGenus17Field.radicand,CommonLiteralField.ell,map_div₀,map_mul,
      div_eq_mul_inv,map_inv₀,eq_ratCast,map_ratCast]
  have haf : rationalEval w hw a = u^2 := by
    change rationalEval w hw (e * algebraMap ℚ A κ⁻¹) = _
    rw [map_mul,(rationalEval w hw).commutes,hve']
    simpa only [div_eq_mul_inv,eq_ratCast,Rat.cast_id] using hu.symm
  haveI : IsLocalHom (rationalEval w hw).toRingHom := IsLocalHom.of_surjective _
    (RationalPlacePoint.valuation_eval_surjective w (rationalEval w hw).toRingHom)
  have haunit : IsUnit a := isUnit_of_map_unit (rationalEval w hw).toRingHom a
    (isUnit_iff_ne_zero.mpr (by
      change rationalEval w hw a ≠ 0
      rw [haf]
      exact pow_ne_zero 2 (ne_of_gt hupos)))
  have hns : ¬ IsSquare (a : F) := by
    rw [haF]
    exact CommonGenus17Field.radicand_nonsquare ℚ (by linarith) (by linarith) (by linarith) (ne_of_gt hκpos)
  have hz : (Genus17PowerBasis.basis t κ).gen^2 = algebraMap F E (a : F) := by
    rw [Genus17PowerBasis.gen_eq,haF]
    exact fifthRoot_sq t κ
  obtain ⟨v,hv,hvRat,z,hzv,hzeval⟩ := QuadraticPlaceExtension.exists_rational_place w hw
    (Genus17PowerBasis.basis t κ)
    (Genus17PowerBasis.dim_eq_two t κ (by linarith) (by linarith) (by linarith) (ne_of_gt hκpos))
    a haunit hns hz u haf.symm
  exact ⟨v,hv,hvRat,u,hupos,z,hzv.trans (Genus17PowerBasis.gen_eq t κ),hzeval⟩

end FourCorner.Genus17PlaceLift
#print axioms FourCorner.Genus17PlaceLift.rational_place_lifts
