import RationalPlacePoint

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.RationalCoordinateLift
open CommonRationalPlace CommonPostPointResidue CurveRationalPlace07

theorem evaluation_congr {F : Type*} [Field F] [Algebra ℚ F]
    {w v : Place ℚ F} (h : w = v) (hw : w.IsRational) (hv : v.IsRational)
    (a : w.toValuationSubring) (b : v.toValuationSubring) (hab : (a : F) = b) :
    rationalEval w hw a = rationalEval v hv b := by
  subst v
  have he : a = b := Subtype.ext hab
  subst b
  rfl

theorem regular_value {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (p : Spec (.of ℚ) ⟶ M.C)
    (a : (pointPlace M p).toValuationSubring) :
    ∃ s : M.C.presheaf.stalk (pointCenter M p).1,
      algebraMap (M.C.presheaf.stalk (pointCenter M p).1) M.C.functionField s = M.ffEquiv (a : F) ∧
      (Scheme.stalkClosedPointTo p).hom s = rationalEval (pointPlace M p) (pointPlace_rational M p) a := by
  refine ⟨(stalkValuationEquiv M (pointCenter M p)).symm a,
    stalkValuationEquiv_symm_image M (pointCenter M p) a,?_⟩
  change pointValuationEval M p a = _
  rw [valuation_eval_eq (pointPlace M p) (pointPlace_rational M p) (pointValuationEval M p)]
  rfl

theorem regular_value_of_place_eq {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (p : Spec (.of ℚ) ⟶ M.C) (w : Place ℚ F) (hw : w.IsRational)
    (h : pointPlace M p = w) (a : w.toValuationSubring) :
    ∃ s : M.C.presheaf.stalk (pointCenter M p).1,
      algebraMap (M.C.presheaf.stalk (pointCenter M p).1) M.C.functionField s = M.ffEquiv (a : F) ∧
      (Scheme.stalkClosedPointTo p).hom s = rationalEval w hw a := by
  let b : (pointPlace M p).toValuationSubring := ⟨(a : F),by rw [h]; exact a.property⟩
  obtain ⟨s,hs,hv⟩ := regular_value M p b
  exact ⟨s,hs,hv.trans (evaluation_congr h (pointPlace_rational M p) hw b a rfl)⟩

variable {F E : Type*} [Field F] [Field E] [Algebra ℚ F] [Algebra ℚ E]
  [Algebra F E] [IsScalarTower ℚ F E] [Algebra.IsIntegral F E]

/-- Restricting the same chosen place preserves every original coordinate's
actual local-stalk value at the original and lifted scheme points. -/
theorem included_regular_value (M : CurveModel ℚ F) (N : CurveModel ℚ E)
    (p : Spec (.of ℚ) ⟶ M.C) (q : Spec (.of ℚ) ⟶ N.C)
    (hr : (pointPlace N q).restrict F = pointPlace M p)
    (a : (pointPlace M p).toValuationSubring) :
    ∃ s : N.C.presheaf.stalk (pointCenter N q).1,
      algebraMap (N.C.presheaf.stalk (pointCenter N q).1) N.C.functionField s =
        N.ffEquiv (algebraMap F E (a : F)) ∧
      (Scheme.stalkClosedPointTo q).hom s = pointValuationEval M p a := by
  let w := pointPlace N q
  have hw := pointPlace_rational N q
  have hw0 : (w.restrict F).IsRational := hr.symm ▸ pointPlace_rational M p
  let a0 : (w.restrict F).toValuationSubring := ⟨(a : F),by rw [hr]; exact a.property⟩
  let b := Place.restrictInclusion F w a0
  let f0 := (rationalEval w hw).toRingHom.comp (Place.restrictInclusion F w)
  have hf0 := valuation_eval_eq (w.restrict F) hw0 f0
  have hb : rationalEval w hw b = rationalEval (w.restrict F) hw0 a0 := by
    change f0 a0 = _
    rw [hf0]
    rfl
  have hbase : rationalEval (w.restrict F) hw0 a0 =
      rationalEval (pointPlace M p) (pointPlace_rational M p) a :=
    evaluation_congr hr hw0 (pointPlace_rational M p) a0 a rfl
  obtain ⟨s,hs,hv⟩ := regular_value N q b
  refine ⟨s,hs,?_⟩
  calc
    (Scheme.stalkClosedPointTo q).hom s = rationalEval w hw b := hv
    _ = rationalEval (pointPlace M p) (pointPlace_rational M p) a := hb.trans hbase
    _ = pointValuationEval M p a := by
      change (rationalEval (pointPlace M p) (pointPlace_rational M p)).toRingHom a = _
      rw [← valuation_eval_eq (pointPlace M p) (pointPlace_rational M p) (pointValuationEval M p)]

end FourCorner.RationalCoordinateLift
#print axioms FourCorner.RationalCoordinateLift.regular_value_of_place_eq
#print axioms FourCorner.RationalCoordinateLift.included_regular_value
