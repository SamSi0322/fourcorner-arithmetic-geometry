import RationalPlaceSource07
import CommonPostPointResidue

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.CommonPointSource
open CommonLiteralField CommonRationalPlace CommonPostPointResidue CurveRationalPlace07

/-- The literal order is ell, P, C, M, B, with the four roots retained separately. -/
def orderedFunction (t : ℚ) : Fin 5 → field ℚ t := ![ell ℚ t,
  root ℚ t 0,root ℚ t 1,root ℚ t 2,root ℚ t 3]

def orderedValue {t : ℚ} (S : CommonRootSource ℚ t) : Fin 5 → ℚ :=
  ![S.ell,S.P,S.C,S.M,S.B]

/-- Extract the complete ordered source from the precise place of the supplied
actual scheme point. No choice of another place or another ell is involved. -/
def source (t : ℚ) (ht : 1 < t) (M : CurveModel ℚ (field ℚ t))
    (p : Spec (.of ℚ) ⟶ M.C) : CommonRootSource ℚ t :=
  rationalPlaceSource07 t ht (pointPlace M p) (pointPlace_rational M p)

/-- All five source values are residues of the original five literal functions
at this same point-specific valuation ring. -/
theorem rational_place_coordinate (t : ℚ) (ht : 1 < t)
    (w : Place ℚ (field ℚ t)) (hw : w.IsRational) (i : Fin 5) :
    ∃ a : w.toValuationSubring,
      (a : field ℚ t) = orderedFunction t i ∧
      rationalEval w hw a = orderedValue (rationalPlaceSource07 t ht w hw) i := by
  fin_cases i <;>
    dsimp [orderedFunction,orderedValue,rationalPlaceSource07] <;>
    exact ⟨_,rfl,rfl⟩

/-- Each extracted coordinate is the actual pullback of a local representative
of that literal function under the original rational point. -/
theorem actual_point_coordinates (t : ℚ) (ht : 1 < t)
    (M : CurveModel ℚ (field ℚ t)) (p : Spec (.of ℚ) ⟶ M.C) (i : Fin 5) :
    ∃ a : M.C.presheaf.stalk (pointCenter M p).1,
      algebraMap (M.C.presheaf.stalk (pointCenter M p).1) M.C.functionField a =
        M.ffEquiv (orderedFunction t i) ∧
      (Scheme.stalkClosedPointTo p).hom a = orderedValue (source t ht M p) i := by
  let w := pointPlace M p
  have hw : w.IsRational := pointPlace_rational M p
  obtain ⟨a,ha,hv⟩ := rational_place_coordinate t ht w hw i
  refine ⟨(stalkValuationEquiv M (pointCenter M p)).symm a,?_,?_⟩
  · rw [stalkValuationEquiv_symm_image,ha]
  · change pointValuationEval M p a = _
    rw [valuation_eval_eq w hw (pointValuationEval M p)]
    exact hv

/-- Rational-field algebra structures are unique; this wrapper keeps the
original model's chosen algebra instance without changing its scheme or point. -/
def sourceForAlgebra (t : ℚ) (ht : 1 < t) (a : Algebra ℚ (field ℚ t)) :
    letI := a
    (M : CurveModel ℚ (field ℚ t)) → (Spec (.of ℚ) ⟶ M.C) → CommonRootSource ℚ t := by
  have ha : a = (DivisionRing.toRatAlgebra : Algebra ℚ (field ℚ t)) := Subsingleton.elim _ _
  subst a
  exact source t ht

theorem actual_point_coordinates_forAlgebra (t : ℚ) (ht : 1 < t)
    (a : Algebra ℚ (field ℚ t)) :
    letI := a
    ∀ (M : CurveModel ℚ (field ℚ t)) (p : Spec (.of ℚ) ⟶ M.C) (i : Fin 5),
    ∃ b : M.C.presheaf.stalk (pointCenter M p).1,
      algebraMap (M.C.presheaf.stalk (pointCenter M p).1) M.C.functionField b =
        M.ffEquiv (orderedFunction t i) ∧
      (Scheme.stalkClosedPointTo p).hom b = orderedValue (sourceForAlgebra t ht a M p) i := by
  have ha : a = (DivisionRing.toRatAlgebra : Algebra ℚ (field ℚ t)) := Subsingleton.elim _ _
  subst a
  exact actual_point_coordinates t ht

end FourCorner.CommonPointSource
#print axioms FourCorner.CommonPointSource.source
#print axioms FourCorner.CommonPointSource.rational_place_coordinate
#print axioms FourCorner.CommonPointSource.actual_point_coordinates
#print axioms FourCorner.CommonPointSource.actual_point_coordinates_forAlgebra
