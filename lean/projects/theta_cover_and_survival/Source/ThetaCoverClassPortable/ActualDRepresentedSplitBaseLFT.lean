import ThetaCoverClassPortable.ActualDRepresentedSplitBase
import ThetaCoverClassPortable.ActualPicardLocallyFiniteType

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
namespace FourCorner.DActualOpenChartCompletion

/-- Append-only strengthening of the actual split-base representation: its
structural map is locally of finite type, derived from actual cut descent. -/
theorem exists_actual_split_representation_lft :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℚ A) (_ : Module.Finite ℚ A)
      (_ : Algebra.Etale ℚ A) (_ : Module.FaithfullyFlat ℚ A)
      (_ : IsNoetherianRing A) (_ : _root_.IsReduced A),
      let c := SmoothProperCurve.baseChange ℚ DRationalInputs.toBase A
      let ε := SmoothProperCurve.sectionBaseChange A DRationalInputs.OD
      ∃ D : RelativePic0Designation A c,
        Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧ LocallyOfFiniteType D.toBase := by
  obtain ⟨A,_,_,_,_,_,_,_,D,⟨hD⟩⟩ := exists_actual_split_representation
  letI := DRationalInputs.proper
  letI := DRationalInputs.smooth
  letI := DRationalInputs.geometricallyIntegral
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  exact ⟨A,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,D,⟨hD⟩,
    ActualPicardLocallyFiniteType.solution A _ _
      ((DRationalInputs.actual_finiteMapData 0).baseChange A) D hD⟩

#print axioms exists_actual_split_representation_lft
end FourCorner.DActualOpenChartCompletion
