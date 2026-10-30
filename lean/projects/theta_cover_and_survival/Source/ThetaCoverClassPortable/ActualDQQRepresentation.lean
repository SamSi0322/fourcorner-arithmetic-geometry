import ThetaCoverClassPortable.DActualQQDescentOfAF
import ThetaCoverClassPortable.ActualDRepresentedPropertiesAF
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
namespace FourCorner.ActualDQQRepresentation

/-- Unconditional representation of the original literal D/QQ and OD.
The same genuinely constructed finite-etale split-base witness supplies AF;
there is no representation, AF or geometric-property hypothesis. -/
theorem exists_representation :
    ∃ J : RelativePic0Designation ℚ DRationalInputs.toBase,
      Nonempty (RepresentsRelSubPic DRationalInputs.toBase DRationalInputs.OD
        (algEquivZeroCut DRationalInputs.toBase DRationalInputs.OD) J) ∧
        Smooth J.toBase ∧ IsProper J.toBase ∧ GeometricallyConnected J.toBase := by
  obtain ⟨A,_,_,_,_,_,_,_,D',⟨h'⟩,hlft,_,_,_,_,haff⟩ :=
    ActualPicardProperties.exists_actual_split_representation_properties_AF
  letI := hlft
  obtain ⟨J,hJ,hsm,hpr,hgc,_,_⟩ := DActualQQDescent.of_split_af A D' h' haff
  exact ⟨J,hJ,hsm,hpr,hgc⟩

/-- The actual original D/QQ representer chosen from the proved construction. -/
def designation : RelativePic0Designation ℚ DRationalInputs.toBase :=
  exists_representation.choose

def represents : RepresentsRelSubPic DRationalInputs.toBase DRationalInputs.OD
    (algEquivZeroCut DRationalInputs.toBase DRationalInputs.OD) designation :=
  exists_representation.choose_spec.1.some

theorem smooth : Smooth designation.toBase := exists_representation.choose_spec.2.1
theorem proper : IsProper designation.toBase := exists_representation.choose_spec.2.2.1
theorem geometricallyConnected : GeometricallyConnected designation.toBase :=
  exists_representation.choose_spec.2.2.2

end FourCorner.ActualDQQRepresentation
