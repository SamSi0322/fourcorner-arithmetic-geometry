import CommonPostStalkFields

noncomputable section
namespace FourCorner.CommonPostEllDegree
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CommonPostGeometricGenus CommonPostFiniteP1 CommonPostStalkFields
local instance p1Integral : IsIntegral (ProjectiveLineCharts.P1 ℚ) := ProjectiveLineCharts.integral ℚ
local instance baseRatAlgebra : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

/-- The actual function-field pullback, transported through the field
isomorphisms induced by the two native generic-stalk morphisms. -/
def fieldPullback (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    (ProjectiveLineCharts.P1 ℚ).functionField →+* (commonCurve t h0 h1 hm).functionField :=
  (sourceEquiv t h0 h1 hm).symm.toRingHom.comp ((literalInclusion t).comp baseEquiv.toRingHom)

/-- The pullback is certified by a square at the actual generic stalks. -/
theorem generic_stalk_square (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    (commonCurve t h0 h1 hm).fromSpecStalk (genericPoint (commonCurve t h0 h1 hm)) ≫ ellMap t h0 h1 hm =
      Spec.map (CommRingCat.ofHom (fieldPullback t h0 h1 hm)) ≫
        (ProjectiveLineCharts.P1 ℚ).fromSpecStalk (genericPoint (ProjectiveLineCharts.P1 ℚ)) := by
  let e := sourceEquiv t h0 h1 hm
  have hs : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ sourceFieldPoint t h0 h1 hm =
      (commonCurve t h0 h1 hm).fromSpecStalk (genericPoint (commonCurve t h0 h1 hm)) := by
    rw [← source_factor,← Category.assoc,← Spec.map_comp]
    have he : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact e.symm_apply_apply a
    rw [he]
    simp
  rw [← hs,Category.assoc,generic_ellMap,← base_factor]
  rw [← Category.assoc,← Category.assoc,← Spec.map_comp,← Spec.map_comp]
  rfl

/-- Degree sixteen for the genuine generic-point function fields of the actual
native finite ell morphism, whose pullback is certified above. -/
theorem degree_sixteen (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI := (fieldPullback t h0 h1 hm).toAlgebra
    Module.finrank (ProjectiveLineCharts.P1 ℚ).functionField (commonCurve t h0 h1 hm).functionField = 16 := by
  letI := (fieldPullback t h0 h1 hm).toAlgebra
  have h := Algebra.finrank_eq_of_equiv_equiv baseEquiv.symm (sourceEquiv t h0 h1 hm).symm (by
    apply RingHom.ext
    intro a
    change (sourceEquiv t h0 h1 hm).symm (literalInclusion t (baseEquiv (baseEquiv.symm a))) =
      (sourceEquiv t h0 h1 hm).symm (literalInclusion t a)
    rw [baseEquiv.apply_symm_apply])
  exact h.symm.trans (ell_extension_degree_sixteen t h0 h1 hm)
end FourCorner.CommonPostEllDegree
#print axioms FourCorner.CommonPostEllDegree.fieldPullback
#print axioms FourCorner.CommonPostEllDegree.generic_stalk_square
#print axioms FourCorner.CommonPostEllDegree.degree_sixteen
