import ThetaCoverClassPortable.ThetaQQCoverLineEndpoint
import ThetaCoverClassPortable.ThetaCoverAlgEquivZero
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj
namespace FourCorner.ActualQQCoverPointGroup
open ThetaLiteralModels ThetaQQRigidifiedLine

variable {J : RelativePic0Designation ℚ (dToBase ℚ)}

/-- The same genuine representation, viewed with the proved group cut. -/
def groupRepresentation
    (h : RepresentsRelSubPic (dToBase ℚ) origin (algEquivZeroCut (dToBase ℚ) origin) J) :
    RepresentsRelSubPic (dToBase ℚ) origin (algEquivZeroGroupCut (dToBase ℚ) origin).toSubPicCondition J := h

/-- The native represented group law, transported from actual tensor products. -/
def groupLaw
    (h : RepresentsRelSubPic (dToBase ℚ) origin (algEquivZeroCut (dToBase ℚ) origin) J) :
    RelativeGroupLaw ℚ J.toBase := (groupRepresentation h).relativeGroupLaw

/-- Classification of the original rational rigidified cover line on this same J. -/
def coverPoint
    (h : RepresentsRelSubPic (dToBase ℚ) origin (algEquivZeroCut (dToBase ℚ) origin) J) :
    SchemeHomOver (𝟙 (Spec (.of ℚ))) J.toBase :=
  h.classify (𝟙 (Spec (.of ℚ))) rigidifiedLine ThetaCoverAlgEquivZero.cut_membership

variable (h : RepresentsRelSubPic (dToBase ℚ) origin (algEquivZeroCut (dToBase ℚ) origin) J)

theorem coverPoint_poincare :
    Nonempty ((h.poincare.pullbackAlong (coverPoint h)).L ≅ relativeLine) :=
  h.classify_spec _ _ ThetaCoverAlgEquivZero.cut_membership

theorem groupLaw_commutative {T : Scheme} (t : T ⟶ Spec (.of ℚ))
    (x y : SchemeHomOver t J.toBase) :
    (groupLaw h).mul t x y = (groupLaw h).mul t y x :=
  (groupRepresentation h).relativeGroupLaw_isCommutative t x y

theorem groupLaw_one : ((groupLaw h).one (𝟙 (Spec (.of ℚ)))).val = J.zeroSection :=
  (groupRepresentation h).relativeGroupLaw_one

theorem poincare_one :
    Nonempty ((h.poincare.pullbackAlong ((groupLaw h).one (𝟙 (Spec (.of ℚ))))).L ≅
      (RigidifiedLineBundle.unit (c := dToBase ℚ) (ε := origin) (𝟙 (Spec (.of ℚ)))).L) := by
  exact (groupRepresentation h).nonempty_poincare_pullbackAlong_one_iso (Over.mk (𝟙 (Spec (.of ℚ))))

theorem poincare_mul (x y : SchemeHomOver (𝟙 (Spec (.of ℚ))) J.toBase) :
    Nonempty ((h.poincare.pullbackAlong ((groupLaw h).mul (𝟙 (Spec (.of ℚ))) x y)).L ≅
      (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) := by
  exact (groupRepresentation h).nonempty_poincare_pullbackAlong_mul_iso
    (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

/-- The actual QQ cover point is not the identity, by the proved nontrivial line. -/
theorem coverPoint_ne_one : coverPoint h ≠ (groupLaw h).one (𝟙 (Spec (.of ℚ))) := by
  intro hp
  obtain ⟨ep⟩ := coverPoint_poincare h
  rw [hp] at ep
  exact ThetaQQCoverLineEndpoint.relative_line_nontrivial ⟨ep.symm ≪≫ (poincare_one h).some⟩

/-- Tensor-square triviality of the actual QQ line gives order dividing two
in the native represented point group, through genuine Poincare comparison. -/
theorem coverPoint_mul_self :
    (groupLaw h).mul (𝟙 (Spec (.of ℚ))) (coverPoint h) (coverPoint h) =
      (groupLaw h).one (𝟙 (Spec (.of ℚ))) := by
  apply h.ext_of_iso (𝟙 (Spec (.of ℚ)))
  exact ⟨(poincare_mul h (coverPoint h) (coverPoint h)).some ≪≫
    ((coverPoint_poincare h).some ⊗ᵢ (coverPoint_poincare h).some) ≪≫
    ThetaQQCoverLineEndpoint.relative_square_trivial.some ≪≫ (poincare_one h).some.symm⟩

/-- Nonidentity also holds as an inequality of the actual QQ scheme morphisms. -/
theorem coverPoint_ne_zeroSection : (coverPoint h).val ≠ J.zeroSection := by
  intro hp
  apply coverPoint_ne_one h
  apply Subtype.ext
  exact hp.trans (groupLaw_one h).symm

theorem coverPoint_class :
    (h.representableBy.homEquiv (schemeHomOverToOverHom (coverPoint h))) =
      ThetaCoverAlgEquivZero.rationalSubPicardClass := by
  apply Subtype.ext
  exact Quotient.sound (coverPoint_poincare h)

#print axioms coverPoint_poincare
#print axioms coverPoint_ne_one
#print axioms coverPoint_mul_self
#print axioms coverPoint_class
end FourCorner.ActualQQCoverPointGroup
