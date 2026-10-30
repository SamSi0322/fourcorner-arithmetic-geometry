import ThetaCoverClassPortable.ActualDRepresentedSplitBaseLFT
import ThetaCoverClassPortable.DPostRepresentationProperties

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
namespace FourCorner.ActualPicardProperties

/-- Actual represented split-base D, together with its proved geometric properties.
The finite etale faithfully flat base and representation are constructed by the
accepted split-representation endpoint; the properties use the same designation. -/
theorem exists_actual_split_representation_properties :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℚ A) (_ : Module.Finite ℚ A)
      (_ : Algebra.Etale ℚ A) (_ : Module.FaithfullyFlat ℚ A)
      (_ : IsNoetherianRing A) (_ : _root_.IsReduced A),
      let c := SmoothProperCurve.baseChange ℚ DRationalInputs.toBase A
      let ε := SmoothProperCurve.sectionBaseChange A DRationalInputs.OD
      ∃ D : RelativePic0Designation A c,
        Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        LocallyOfFiniteType D.toBase ∧ Smooth D.toBase ∧ IsProper D.toBase ∧
        GeometricallyConnected D.toBase ∧ IsSeparated D.toBase := by
  obtain ⟨A,_,_,_,_,_,_,_,D,⟨hD⟩,hLFT⟩ :=
    DActualOpenChartCompletion.exists_actual_split_representation_lft
  letI := hLFT
  obtain ⟨hsm,hpr,hgc,hsep⟩ := D_baseChange_postrep_properties A D hD
  exact ⟨A,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,D,⟨hD⟩,hLFT,hsm,hpr,hgc,hsep⟩

#print axioms exists_actual_split_representation_properties
end FourCorner.ActualPicardProperties
