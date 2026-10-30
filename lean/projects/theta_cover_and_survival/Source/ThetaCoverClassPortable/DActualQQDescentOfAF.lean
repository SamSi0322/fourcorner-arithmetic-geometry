import ThetaCoverClassPortable.DActualFiniteFFPicardSheaf
import ThetaCoverClassPortable.FiniteEtalePicardAssembly
import ThetaCoverClassPortable.DPostRepresentationProperties
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
namespace FourCorner.DActualQQDescent

/-- Actual D/QQ descent with only the genuine AF property left at this boundary.
The split-base representation is of the original D base change with OD; all
geometric properties and finite-FF class descent are supplied internally. -/
theorem of_split_af
    (A : Type) [CommRing A] [Algebra ℚ A] [Module.Finite ℚ A]
    [Algebra.Etale ℚ A] [Module.FaithfullyFlat ℚ A] [IsNoetherianRing A]
    (D' : RelativePic0Designation A (baseChange ℚ DRationalInputs.toBase A))
    (h' : RepresentsRelSubPic (baseChange ℚ DRationalInputs.toBase A)
      (sectionBaseChange A DRationalInputs.OD)
      (algEquivZeroCut (baseChange ℚ DRationalInputs.toBase A)
        (sectionBaseChange A DRationalInputs.OD)) D')
    [LocallyOfFiniteType D'.toBase]
    (haff : ∀ S : Finset D'.P, ∃ U : D'.P.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    ∃ J : RelativePic0Designation ℚ DRationalInputs.toBase,
      Nonempty (RepresentsRelSubPic DRationalInputs.toBase DRationalInputs.OD
        (algEquivZeroCut DRationalInputs.toBase DRationalInputs.OD) J) ∧
        Smooth J.toBase ∧ IsProper J.toBase ∧ GeometricallyConnected J.toBase ∧
        ∃ e : pullback J.toBase (specMap ℚ A) ≅ D'.P,
          e.hom ≫ D'.toBase = pullback.snd J.toBase (specMap ℚ A) := by
  obtain ⟨hsm,hpr,hgc,_⟩ := ActualPicardProperties.D_baseChange_postrep_properties A D' h'
  exact FiniteEtalePicardAssembly.of_singleton_sheaf ℚ DRationalInputs.toBase DRationalInputs.OD A
    (DRationalInputs.actual_relSubPic_finiteFF_sheaf A) D' h' hsm hpr hgc haff

end FourCorner.DActualQQDescent
