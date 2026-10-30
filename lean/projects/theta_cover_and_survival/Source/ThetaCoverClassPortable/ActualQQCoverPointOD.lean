import ThetaCoverClassPortable.ActualQQCoverPointGroup
import ThetaCoverClassPortable.DFieldCore

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian
namespace FourCorner.ActualQQCoverPointGroup
open ThetaLiteralModels ThetaQQRigidifiedLine

/-- Both original constructions are the identical actual rational point [1:1:1]. -/
theorem original_origin_eq : DRationalInputs.OD = origin := by
  apply Subtype.ext
  exact ThetaCoverRationalData.rational_origin_preserved.symm

/-- Only equality of the two actual original sections is transported; J and its
actual curve/QQ structural map stay exactly the same. -/
def repAtCoverOrigin
    {J : RelativePic0Designation ℚ DRationalInputs.toBase}
    (h : RepresentsRelSubPic DRationalInputs.toBase DRationalInputs.OD
      (algEquivZeroCut DRationalInputs.toBase DRationalInputs.OD) J) :
    RepresentsRelSubPic (dToBase ℚ) origin (algEquivZeroCut (dToBase ℚ) origin) J := by
  rw [← original_origin_eq]
  exact h

/-- The rational cover point on precisely the designation supplied with the
original OD representation, suitable for an actual unconditional QQ caller. -/
def coverPointAtOD
    {J : RelativePic0Designation ℚ DRationalInputs.toBase}
    (h : RepresentsRelSubPic DRationalInputs.toBase DRationalInputs.OD
      (algEquivZeroCut DRationalInputs.toBase DRationalInputs.OD) J) :
    SchemeHomOver (𝟙 (Spec (.of ℚ))) J.toBase := coverPoint (repAtCoverOrigin h)

theorem original_rep_cover_point
    {J : RelativePic0Designation ℚ DRationalInputs.toBase}
    (h : RepresentsRelSubPic DRationalInputs.toBase DRationalInputs.OD
      (algEquivZeroCut DRationalInputs.toBase DRationalInputs.OD) J) :
    let h' := repAtCoverOrigin h
    let p := coverPointAtOD h
    Nonempty ((h'.poincare.pullbackAlong p).L ≅ relativeLine) ∧
      p ≠ (groupLaw h').one (𝟙 (Spec (.of ℚ))) ∧
      (groupLaw h').mul (𝟙 (Spec (.of ℚ))) p p =
        (groupLaw h').one (𝟙 (Spec (.of ℚ))) :=
  ⟨coverPoint_poincare _,coverPoint_ne_one _,coverPoint_mul_self _⟩

#print axioms original_origin_eq
#print axioms repAtCoverOrigin
#print axioms original_rep_cover_point
end FourCorner.ActualQQCoverPointGroup
