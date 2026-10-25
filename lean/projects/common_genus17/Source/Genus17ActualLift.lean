import Genus17PlaceLift
import RationalCoordinateLift
import Genus17PointMap

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.Genus17ActualLift
open Genus17Geometry CommonPostPointResidue CommonRationalPlace CommonPointSource
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every actual rational point lifts to ONE twist in the exact finite K_t.
The native cover returns precisely that original point; all five ordered
literal functions and the fifth root have actual stalk-value witnesses. -/
theorem actual_point_lifts (t : ℚ) (ht : 1 < t)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI := CommonPostGeometricGenus.modelFieldAlgebra t
    ∀ p : Spec (.of ℚ) ⟶ CommonPostFiniteP1.commonCurve t h0 h1 hm,
    let S := CommonPointSource.sourceForAlgebra t ht
      (CommonPostGeometricGenus.modelFieldAlgebra t) (CommonSchemeModel.model t h0 h1 hm) p
    ∃ κ ∈ Genus17Support.twists t, 0 < κ ∧
      letI := Genus17Geometry.modelFieldAlgebra t κ
      ∃ q : Spec (.of ℚ) ⟶ curve t κ h0 h1 hm,
        q ≫ cover t κ h0 h1 hm = p ∧
        (∃ u : ℚ, 0 < u ∧
          ∃ s : (curve t κ h0 h1 hm).presheaf.stalk (pointCenter (model t κ h0 h1 hm) q).1,
            algebraMap ((curve t κ h0 h1 hm).presheaf.stalk (pointCenter (model t κ h0 h1 hm) q).1)
              (curve t κ h0 h1 hm).functionField s = (model t κ h0 h1 hm).ffEquiv (fifthRoot t κ) ∧
            (Scheme.stalkClosedPointTo q).hom s = u) ∧
        (∀ i : Fin 5,
          ∃ s : (curve t κ h0 h1 hm).presheaf.stalk (pointCenter (model t κ h0 h1 hm) q).1,
            algebraMap ((curve t κ h0 h1 hm).presheaf.stalk (pointCenter (model t κ h0 h1 hm) q).1)
              (curve t κ h0 h1 hm).functionField s =
                (model t κ h0 h1 hm).ffEquiv
                  (algebraMap (baseField t) (field t κ) (orderedFunction t i)) ∧
            (Scheme.stalkClosedPointTo q).hom s = orderedValue S i) := by
  letI := CommonPostGeometricGenus.modelFieldAlgebra t
  intro p S
  let B := CommonSchemeModel.model t h0 h1 hm
  let w := pointPlace B p
  have hw : w.IsRational := pointPlace_rational B p
  obtain ⟨κ,hκ,hκpos,hdata⟩ := Genus17PlaceLift.rational_place_lifts t ht w hw
  refine ⟨κ,hκ,hκpos,?_⟩
  letI := Genus17Geometry.modelFieldAlgebra t κ
  obtain ⟨v,hv,hvRat,u,hupos,z,hz,hzeval⟩ := hdata
  let N := model t κ h0 h1 hm
  let q := RationalPlacePoint.pointOfPlace N v hvRat
  have hq : pointPlace N q = v := RationalPlacePoint.pointOfPlace_place N v hvRat
  have hres : (pointPlace N q).restrict (baseField t) = pointPlace B p := by
    rw [hq,hv]
  have hc : coverClosed t κ h0 h1 hm (pointCenter N q) =
      pointCenter B (q ≫ cover t κ h0 h1 hm) := by
    apply Subtype.ext
    rfl
  have hmap := cover_point_restrict t κ h0 h1 hm (pointCenter N q)
  change (pointPlace N q).restrict (baseField t) =
    B.placeOfPoint (coverClosed t κ h0 h1 hm (pointCenter N q)) at hmap
  rw [hc] at hmap
  have hcomp : q ≫ cover t κ h0 h1 hm = p :=
    RationalPlacePoint.point_place_injective B (hmap.symm.trans hres)
  refine ⟨q,hcomp,?_,?_⟩
  · obtain ⟨s,hs,hsval⟩ := RationalCoordinateLift.regular_value_of_place_eq N q v hvRat hq z
    exact ⟨u,hupos,s,hs.trans (congrArg N.ffEquiv hz),hsval.trans hzeval⟩
  · intro i
    obtain ⟨a,ha,haval⟩ := RationalPlaceSourceAnyAlgebra.coordinates t ht
      (CommonPostGeometricGenus.modelFieldAlgebra t) w hw i
    have hS : RationalPlaceSourceAnyAlgebra.literalSource t ht
        (CommonPostGeometricGenus.modelFieldAlgebra t) w hw = S :=
      RationalPlaceSourceAnyAlgebra.point_source_eq t ht
        (CommonPostGeometricGenus.modelFieldAlgebra t) B p
    rw [hS] at haval
    have hvalue : pointValuationEval B p a = orderedValue S i := by
      rw [valuation_eval_eq w hw (pointValuationEval B p)]
      exact haval
    obtain ⟨s,hs,hsval⟩ := RationalCoordinateLift.included_regular_value B N p q hres a
    refine ⟨s,?_,hsval.trans hvalue⟩
    simpa only [ha] using hs

end FourCorner.Genus17ActualLift
#print axioms FourCorner.Genus17ActualLift.actual_point_lifts
