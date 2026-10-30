import ThetaCoverClassPortable.ThetaQQRigidifiedLine
import ThetaCoverClassPortable.ThetaKummerWeilComparison
import ThetaCoverClassPortable.LineIsoDescent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace FourCorner.ThetaQQCoverLineEndpoint
open ThetaLiteralModels ThetaQQRigidifiedLine

/-- Genuine nontriviality of the QQ line, detected by its true geometric
pullback and the proved Cartier-to-Weil comparison. -/
theorem rational_line_nontrivial : ¬Nonempty (ThetaQQKummerLine.L ≅ 𝟙_ (D ℚ).Modules) := by
  rintro ⟨e⟩
  apply ThetaKummerWeilComparison.geometric_line_nontrivial
  exact ⟨(Scheme.Modules.pullback ThetaGeometricKummerLine.projection).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso ThetaGeometricKummerLine.projection⟩

theorem relative_line_nontrivial : ¬Nonempty (relativeLine ≅
    SheafOfModules.unit (pullback (dToBase ℚ) (𝟙 (Spec (.of ℚ)))).ringCatSheaf) := by
  rintro ⟨e⟩
  apply rational_line_nontrivial
  exact ⟨LineIsoDescent.descendUnitIso (asIso (pullback.fst (dToBase ℚ) (𝟙 (Spec (.of ℚ))))) ThetaQQKummerLine.L e⟩

/-- A genuine QQ-valued object of the native relative-Picard presheaf. -/
def rationalPicardClass : RelPicard.RigidifiedLineBundle.Classes (dToBase ℚ) origin (𝟙 (Spec (.of ℚ))) :=
  Quotient.mk _ rigidifiedLine

def unitPicardClass : RelPicard.RigidifiedLineBundle.Classes (dToBase ℚ) origin (𝟙 (Spec (.of ℚ))) :=
  Quotient.mk _ (RelPicard.RigidifiedLineBundle.unit _)

theorem rationalPicardClass_ne_unit : rationalPicardClass≠unitPicardClass := by
  intro he
  exact relative_line_nontrivial (Quotient.exact he)

theorem relative_square_trivial : Nonempty (relativeLine ⊗ relativeLine ≅
    𝟙_ (pullback (dToBase ℚ) (𝟙 (Spec (.of ℚ)))).Modules) := by
  obtain ⟨e,_⟩ := ThetaQQKummerLine.square_trivialization
  let f := pullback.fst (dToBase ℚ) (𝟙 (Spec (.of ℚ)))
  exact ⟨Functor.Monoidal.μIso (Scheme.Modules.pullback f) ThetaQQKummerLine.L ThetaQQKummerLine.L ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso f⟩

/-- Effective QQ line, actual rigidification, genuine nonzero class and
actual tensor-square triviality. A represented Jacobian point is not
silently identified with this native presheaf object. -/
theorem actual_rational_cover_line :
    Scheme.Modules.IsInvertible ThetaQQKummerLine.L ∧
    Nonempty (ThetaQQKummerLine.L ⊗ ThetaQQKummerLine.L ≅ 𝟙_ (D ℚ).Modules) ∧
    rationalPicardClass≠unitPicardClass ∧
    Nonempty (relativeLine ⊗ relativeLine ≅ 𝟙_ (pullback (dToBase ℚ) (𝟙 (Spec (.of ℚ)))).Modules) := by
  exact ⟨ThetaQQKummerLine.L_invertible,⟨ThetaQQKummerLine.square_trivialization.choose⟩,
    rationalPicardClass_ne_unit,relative_square_trivial⟩

#print axioms actual_rational_cover_line
end FourCorner.ThetaQQCoverLineEndpoint
