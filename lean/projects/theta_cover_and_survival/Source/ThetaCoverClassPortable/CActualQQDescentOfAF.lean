import ThetaCoverClassPortable.CActualFiniteFFPicardSheaf
import ThetaCoverClassPortable.FiniteEtalePicardAssembly
import ThetaCoverClassPortable.CPostRepresentationProperties
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
namespace FourCorner.CActualQQDescent

/-- Actual C/QQ descent with only the genuine AF property left at this boundary.
The split-base representation is of the original C base change with native OC; all
geometric properties and finite-FF class descent are supplied internally. -/
theorem of_split_af
    (A : Type) [CommRing A] [Algebra ℚ A] [Module.Finite ℚ A]
    [Algebra.Etale ℚ A] [Module.FaithfullyFlat ℚ A] [IsNoetherianRing A]
    (D' : RelativePic0Designation A (baseChange ℚ (ThetaLiteralModels.cToBase ℚ) A))
    (h' : RepresentsRelSubPic (baseChange ℚ (ThetaLiteralModels.cToBase ℚ) A)
      (sectionBaseChange A ThetaRationalPicardInput.OC)
      (algEquivZeroCut (baseChange ℚ (ThetaLiteralModels.cToBase ℚ) A)
        (sectionBaseChange A ThetaRationalPicardInput.OC)) D')
    [LocallyOfFiniteType D'.toBase]
    (haff : ∀ S : Finset D'.P, ∃ U : D'.P.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    ∃ J : RelativePic0Designation ℚ (ThetaLiteralModels.cToBase ℚ),
      Nonempty (RepresentsRelSubPic (ThetaLiteralModels.cToBase ℚ) ThetaRationalPicardInput.OC
        (algEquivZeroCut (ThetaLiteralModels.cToBase ℚ) ThetaRationalPicardInput.OC) J) ∧
        Smooth J.toBase ∧ IsProper J.toBase ∧ GeometricallyConnected J.toBase ∧
        ∃ e : pullback J.toBase (specMap ℚ A) ≅ D'.P,
          e.hom ≫ D'.toBase = pullback.snd J.toBase (specMap ℚ A) := by
  obtain ⟨hsm,hpr,hgc,_⟩ := ActualPicardProperties.C_baseChange_postrep_properties A D' h'
  exact FiniteEtalePicardAssembly.of_singleton_sheaf ℚ (ThetaLiteralModels.cToBase ℚ) ThetaRationalPicardInput.OC A
    (ThetaRationalPicardInput.actual_relSubPic_finiteFF_sheaf A) D' h' hsm hpr hgc haff

end FourCorner.CActualQQDescent
