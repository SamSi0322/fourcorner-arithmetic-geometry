import CommonPointSource

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.RationalPlaceSourceAnyAlgebra
open CommonLiteralField CommonPointSource CommonPostPointResidue CommonRationalPlace

def literalSource (t : ℚ) (ht : 1 < t) (a : Algebra ℚ (field ℚ t)) :
    letI := a
    (w : Place ℚ (field ℚ t)) → w.IsRational → CommonRootSource ℚ t := by
  have ha : a = (DivisionRing.toRatAlgebra : Algebra ℚ (field ℚ t)) := Subsingleton.elim _ _
  subst a
  exact rationalPlaceSource07 t ht

theorem coordinates (t : ℚ) (ht : 1 < t) (a : Algebra ℚ (field ℚ t)) :
    letI := a
    ∀ (w : Place ℚ (field ℚ t)) (hw : w.IsRational) (i : Fin 5),
    ∃ b : w.toValuationSubring, (b : field ℚ t) = orderedFunction t i ∧
      rationalEval w hw b = orderedValue (literalSource t ht a w hw) i := by
  have ha : a = (DivisionRing.toRatAlgebra : Algebra ℚ (field ℚ t)) := Subsingleton.elim _ _
  subst a
  exact rational_place_coordinate t ht

theorem point_source_eq (t : ℚ) (ht : 1 < t) (a : Algebra ℚ (field ℚ t)) :
    letI := a
    ∀ (M : CurveModel ℚ (field ℚ t)) (p : Spec (.of ℚ) ⟶ M.C),
      literalSource t ht a (pointPlace M p) (pointPlace_rational M p) =
        CommonPointSource.sourceForAlgebra t ht a M p := by
  have ha : a = (DivisionRing.toRatAlgebra : Algebra ℚ (field ℚ t)) := Subsingleton.elim _ _
  subst a
  intro M p
  rfl

end FourCorner.RationalPlaceSourceAnyAlgebra
#print axioms FourCorner.RationalPlaceSourceAnyAlgebra.coordinates
#print axioms FourCorner.RationalPlaceSourceAnyAlgebra.point_source_eq
