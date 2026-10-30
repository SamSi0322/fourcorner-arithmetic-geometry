import ThetaCoverClassPortable.ActualDRepresentedProperties
import ThetaCoverClassPortable.DPostRepresentationAF
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
namespace FourCorner.ActualPicardProperties

/-- Constructed same actual split-base represented D, with the proved geometric
properties and affine-neighbourhood property. No target property is an input. -/
theorem exists_actual_split_representation_properties_AF :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℚ A) (_ : Module.Finite ℚ A)
      (_ : Algebra.Etale ℚ A) (_ : Module.FaithfullyFlat ℚ A)
      (_ : IsNoetherianRing A) (_ : _root_.IsReduced A),
      let c := SmoothProperCurve.baseChange ℚ DRationalInputs.toBase A
      let ε := SmoothProperCurve.sectionBaseChange A DRationalInputs.OD
      ∃ D : RelativePic0Designation A c,
        Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        LocallyOfFiniteType D.toBase ∧ Smooth D.toBase ∧ IsProper D.toBase ∧
        GeometricallyConnected D.toBase ∧ IsSeparated D.toBase ∧
        ∀ S : Finset D.P, ∃ U : D.P.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := by
  obtain ⟨A,_,_,_,_,_,_,_,D,⟨h⟩,hlft,hsm,hpr,hgc,hsep⟩ := exists_actual_split_representation_properties
  exact ⟨A,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,D,⟨h⟩,hlft,hsm,hpr,hgc,hsep,D_baseChange_exists_isAffineOpen A D h⟩

#print axioms exists_actual_split_representation_properties_AF
end FourCorner.ActualPicardProperties
