import ThetaCoverClassPortable.ActualPicardRepresentation
import ThetaCoverClassPortable.ActualProperDivisorParameter
import ThetaCoverClassPortable.ThetaActualZariskiPicardSheaf
import ThetaCoverClassPortable.ActualRelativeOpenChartInputs
import ThetaCoverClassPortable.ActualPicardLocallyFiniteType

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
namespace FourCorner.CActualRationalInputsCompletion

/-- Exact unbounded finite-map input, on literal original C and native OC. -/
theorem actual_hF : ∀m0:ℕ,∃F:SmoothProperCurve.FiniteMapData
    (ThetaLiteralModels.cToBase ℚ) ThetaRationalPicardInput.OC,m0≤F.m := by
  intro m0
  exact ⟨ThetaRationalPicardInput.actual_finiteMapData m0,
    (ThetaRationalPicardInput.actual_finiteMapData_rank_gt m0).le⟩

/-- Genuine representation of original C after the stated coefficient change.
Genus five and r=11 are native C inputs; no representation is assumed. -/
def represented_after_baseChange
    (A : Type) [CommRing A] [Algebra ℚ A] [IsNoetherianRing A] [_root_.IsReduced A]
    (n : ℕ)
    (γ : Fin n → Fin (11-5) → SchemeHomOver (𝟙 _) (SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) A))
    (hγ : HasChartSections (g:=5) (r:=11) (SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) A) γ) :=
  let c := SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) A
  let ε := SmoothProperCurve.sectionBaseChange A ThetaRationalPicardInput.OC
  letI := ThetaRationalPicardInput.source_proper
  letI := ThetaRationalPicardInput.source_smooth
  letI := ThetaRationalPicardInput.source_geometricallyIntegral
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  let hF : ∀m0:ℕ,∃F:SmoothProperCurve.FiniteMapData c ε,m0≤F.m := fun m0 => by
    obtain ⟨F,h⟩ := actual_hF m0
    exact ⟨F.baseChange A,h⟩
  ActualPicardRepresentation.exists_represented A c ε hF n 5 11 (by decide) γ hγ
    (fun d => by
      obtain ⟨Y,y,D,hD,-⟩ := ActualOpenChartCompletion.actual_ringBase_proper_universal_divisor A d
      exact ⟨Y,y,D,hD⟩)
    (ThetaRationalPicardInput.actual_basechanged_relSubPic_zariski_sheaf A)

theorem exists_actual_split_representation :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℚ A) (_ : Module.Finite ℚ A)
      (_ : Algebra.Etale ℚ A) (_ : Module.FaithfullyFlat ℚ A)
      (_ : IsNoetherianRing A) (_ : _root_.IsReduced A),
      let c := SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) A
      let ε := SmoothProperCurve.sectionBaseChange A ThetaRationalPicardInput.OC
      ∃ D : RelativePic0Designation A c,
        Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) := by
  obtain ⟨A,_,_,_,_,_,_,_,hp,hs,hgi,hF,n,γ,hγ,hcov⟩ :=
    ThetaRationalPicardInput.actual_family_with_curve_relative_affines
  exact ⟨A,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,represented_after_baseChange A n γ hγ⟩

/-- Append-only strengthening of the actual split-base representation: its
structural map is locally of finite type, derived from actual cut descent. -/
theorem exists_actual_split_representation_lft :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℚ A) (_ : Module.Finite ℚ A)
      (_ : Algebra.Etale ℚ A) (_ : Module.FaithfullyFlat ℚ A)
      (_ : IsNoetherianRing A) (_ : _root_.IsReduced A),
      let c := SmoothProperCurve.baseChange ℚ (ThetaLiteralModels.cToBase ℚ) A
      let ε := SmoothProperCurve.sectionBaseChange A ThetaRationalPicardInput.OC
      ∃ D : RelativePic0Designation A c,
        Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧ LocallyOfFiniteType D.toBase := by
  obtain ⟨A,_,_,_,_,_,_,_,D,⟨hD⟩⟩ := exists_actual_split_representation
  letI := ThetaRationalPicardInput.source_proper
  letI := ThetaRationalPicardInput.source_smooth
  letI := ThetaRationalPicardInput.source_geometricallyIntegral
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  exact ⟨A,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,D,⟨hD⟩,
    ActualPicardLocallyFiniteType.solution A _ _
      ((ThetaRationalPicardInput.actual_finiteMapData 0).baseChange A) D hD⟩


#print axioms actual_hF
#print axioms exists_actual_split_representation_lft
#print axioms represented_after_baseChange
#print axioms exists_actual_split_representation
end FourCorner.CActualRationalInputsCompletion
