import ThetaCoverClassPortable.DChartSections
import ThetaCoverClassPortable.DFiniteMapBaseChange

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
namespace FourCorner.DRationalInputs
open ThetaLiteralModels AlgebraicGeometry.RelPicard

/-- All EXPLICIT reduced-base family inputs are constructed simultaneously
on the SAME actual finite-etale R'/Q and SAME basechanged original D/OD.
This theorem does not assert existence/AF/descent of any Picard space. -/
theorem actual_reduced_base_family_inputs :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra ℚ R') (_ : Module.Finite ℚ R')
      (_ : Algebra.Etale ℚ R') (_ : Module.FaithfullyFlat ℚ R')
      (_ : IsNoetherianRing R') (_ : _root_.IsReduced R'),
      let cR := SmoothProperCurve.baseChange ℚ toBase R'
      let εR := SmoothProperCurve.sectionBaseChange R' OD
      IsProper cR ∧ SmoothOfRelativeDimension 1 cR ∧ GeometricallyIntegral cR ∧
      (∀ m0 : ℕ, ∃ F : SmoothProperCurve.FiniteMapData cR εR,m0≤F.m ∧ IsUnit (F.m:R')) ∧
      ∃ (n : ℕ) (γ : Fin n → Fin (7-3) → SchemeHomOver (𝟙 _) cR),
        HasChartSections (g:=3) (r:=7) cR γ := by
  obtain ⟨R',_,_,_,_,_,_,_,n,γ,hγ⟩ := actual_finiteEtale_HasChartSections
  letI := proper
  letI := smooth
  letI := geometricallyIntegral
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  refine ⟨R',inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,?_,?_,?_,actual_unbounded_finiteMapData_baseChange R',n,γ,hγ⟩
  · exact MorphismProperty.pullback_snd toBase (SmoothProperCurve.specMap ℚ R') proper
  · exact MorphismProperty.pullback_snd toBase (SmoothProperCurve.specMap ℚ R') smooth
  · exact MorphismProperty.pullback_snd toBase (SmoothProperCurve.specMap ℚ R') geometricallyIntegral

#print axioms actual_reduced_base_family_inputs
end FourCorner.DRationalInputs
