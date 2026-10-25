import Genus17GeometryComplete
import Genus17ActualLift
import Genus17TwistsPositive

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.CommonGenus17Full
open Genus17Geometry CommonPostPointResidue CommonPointSource
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Paper prop:common-genus17 and eq:common-genus17 on the native complete
models and their original finite cover: exact finite twist domain, every
geometric double cover, and actual same-point ordered rational lifting. -/
theorem common_genus17 (t : ℚ) (ht : 1 < t)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI := CommonPostGeometricGenus.modelFieldAlgebra t
    (∀ p : ℕ, p ∈ Genus17Support.oddSupport (t^2-1) ↔
      p.Prime ∧ p ≠ 2 ∧ 0 < padicValRat p (t^2-1) ∧ Odd (padicValRat p (t^2-1))) ∧
    (∀ κ : ℚ, κ ∈ Genus17Support.twists t ↔
      ∃ (e : Bool) (S : Finset ℕ), S ⊆ Genus17Support.oddSupport (t^2-1) ∧
        κ = (if e then 2 else 1) * ∏ p ∈ S, (p : ℚ)) ∧
    (∀ κ ∈ Genus17Support.twists t,
    letI := modelFieldAlgebra t κ
    GeometricallyConnected (toBase t κ h0 h1 hm) ∧
    IsProper (toBase t κ h0 h1 hm) ∧ SmoothOfRelativeDimension 1 (toBase t κ h0 h1 hm) ∧
    IsFinite (cover t κ h0 h1 hm) ∧
    (cover t κ h0 h1 hm ≫ CommonSchemeModel.modelToBase t h0 h1 hm = toBase t κ h0 h1 hm) ∧
    ((curve t κ h0 h1 hm).fromSpecStalk (genericPoint (curve t κ h0 h1 hm)) ≫ cover t κ h0 h1 hm =
      Spec.map (CommRingCat.ofHom (coverFieldPullback t κ h0 h1 hm)) ≫
        (CommonSchemeModel.model t h0 h1 hm).C.fromSpecStalk (genericPoint (CommonSchemeModel.model t h0 h1 hm).C)) ∧
    (letI := (coverFieldPullback t κ h0 h1 hm).toAlgebra
     Module.finrank (CommonSchemeModel.model t h0 h1 hm).C.functionField (curve t κ h0 h1 hm).functionField = 2) ∧
    (letI := (coverFieldPullback t κ h0 h1 hm).toAlgebra
     Module.Finite (CommonSchemeModel.model t h0 h1 hm).C.functionField (curve t κ h0 h1 hm).functionField ∧
       Algebra.IsSeparable (CommonSchemeModel.model t h0 h1 hm).C.functionField (curve t κ h0 h1 hm).functionField) ∧
    (∀ x : closedPoints (curve t κ h0 h1 hm),
      ((model t κ h0 h1 hm).placeOfPoint x).restrict (baseField t) =
        (CommonSchemeModel.model t h0 h1 hm).placeOfPoint (coverClosed t κ h0 h1 hm x) ∧
      ((model t κ h0 h1 hm).placeOfPoint x).ramificationIndex (baseField t) = 1 ∧
      Module.Finite (((model t κ h0 h1 hm).placeOfPoint x).restrict (baseField t)).ResidueField
        ((model t κ h0 h1 hm).placeOfPoint x).ResidueField ∧
      Algebra.IsSeparable (((model t κ h0 h1 hm).placeOfPoint x).restrict (baseField t)).ResidueField
        ((model t κ h0 h1 hm).placeOfPoint x).ResidueField) ∧
    (let c := Genus17GeometricGenus.geometricToBase t κ h0 h1 hm
     letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
     Module.Finite (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) ∧
       Module.finrank (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) = 17) ∧
    (∀ b : baseField t,
      coverFieldPullback t κ h0 h1 hm ((targetFieldEquiv t h0 h1 hm).symm b) =
        (sourceFieldEquiv t κ h0 h1 hm).symm (fieldInclusion t κ b)) ∧
    fifthRoot t κ ^ 2 = ell t κ / algebraMap ℚ (field t κ) κ) ∧
    (    ∀ p : Spec (.of ℚ) ⟶ CommonPostFiniteP1.commonCurve t h0 h1 hm,
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
            (Scheme.stalkClosedPointTo q).hom s = orderedValue S i)) := by
  letI := CommonPostGeometricGenus.modelFieldAlgebra t
  refine ⟨fun p => Genus17Support.mem_oddSupport (t^2-1) p,
    fun κ => Genus17Support.mem_twists,?_,?_⟩
  · intro κ hκ
    exact common_genus17_geometry_complete t κ h0 h1 hm (Genus17Support.twist_ne_zero hκ)
  · exact Genus17ActualLift.actual_point_lifts t ht h0 h1 hm

end FourCorner.CommonGenus17Full
#print axioms FourCorner.CommonGenus17Full.common_genus17
#check FourCorner.CommonGenus17Full.common_genus17
