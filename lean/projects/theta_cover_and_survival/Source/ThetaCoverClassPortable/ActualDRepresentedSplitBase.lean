import ThetaCoverClassPortable.ActualPicardRepresentation
import ThetaCoverClassPortable.ActualDGlobalUniversalDivisor
import ThetaCoverClassPortable.DActualZariskiPicardSheaf
import ThetaCoverClassPortable.DRelativeOpenChartInputs

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
namespace FourCorner.DActualOpenChartCompletion

def represented_after_baseChange
    (A : Type) [CommRing A] [Algebra ℚ A] [IsNoetherianRing A] [_root_.IsReduced A]
    (n : ℕ)
    (γ : Fin n → Fin (7-3) → SchemeHomOver (𝟙 _) (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase A))
    (hγ : HasChartSections (g:=3) (r:=7) (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase A) γ) :=
  let c := SmoothProperCurve.baseChange ℚ DRationalInputs.toBase A
  let ε := SmoothProperCurve.sectionBaseChange A DRationalInputs.OD
  letI := DRationalInputs.proper
  letI := DRationalInputs.smooth
  letI := DRationalInputs.geometricallyIntegral
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  let hF : ∀m0:ℕ,∃F:SmoothProperCurve.FiniteMapData c ε,m0≤F.m := fun m0 => by
    obtain ⟨F,h⟩ := DRationalInputs.actual_hF m0
    exact ⟨F.baseChange A,h⟩
  ActualPicardRepresentation.exists_represented A c ε hF n 3 7 (by decide) γ hγ
    (fun d => by
      obtain ⟨Y,y,D,hD,-⟩ := DRationalInputs.actual_ringBase_proper_universal_divisor A d
      exact ⟨Y,y,D,hD⟩)
    (DRationalInputs.actual_basechanged_relSubPic_zariski_sheaf A)

theorem exists_actual_split_representation :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℚ A) (_ : Module.Finite ℚ A)
      (_ : Algebra.Etale ℚ A) (_ : Module.FaithfullyFlat ℚ A)
      (_ : IsNoetherianRing A) (_ : _root_.IsReduced A),
      let c := SmoothProperCurve.baseChange ℚ DRationalInputs.toBase A
      let ε := SmoothProperCurve.sectionBaseChange A DRationalInputs.OD
      ∃ D : RelativePic0Designation A c,
        Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) := by
  obtain ⟨A,_,_,_,_,_,_,_,hp,hs,hgi,hF,n,γ,hγ,hcov⟩ :=
    DRationalInputs.actual_family_with_curve_relative_affines
  exact ⟨A,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,represented_after_baseChange A n γ hγ⟩

#print axioms represented_after_baseChange
#print axioms exists_actual_split_representation
end FourCorner.DActualOpenChartCompletion
