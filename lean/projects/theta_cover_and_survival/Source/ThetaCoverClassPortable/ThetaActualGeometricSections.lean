import ThetaCoverClassPortable.FiniteMapGeometricSections
import ThetaCoverClassPortable.ThetaFiniteEtaleInput
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra
namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels

theorem actual_levelSet_closedImmersion
    (𝔉 : SmoothProperCurve.FiniteMapData (cToBase ℚ) OC) (s : ℚ) :
    IsClosedImmersion (𝔉.levelSetIntoCurve s) := by
  haveI : IsProper (cToBase ℚ) := source_proper
  haveI : IsSeparated (cToBase ℚ) := inferInstance
  infer_instance

theorem actual_exists_finiteEtale_geometric_sections
    (𝔉 : SmoothProperCurve.FiniteMapData (cToBase ℚ) OC) (hm : 0 < 𝔉.m) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra ℚ R') (_ : Module.Finite ℚ R')
      (_ : Algebra.Etale ℚ R') (_ : Module.FaithfullyFlat ℚ R') (_ : IsNoetherianRing R')
      (_ : _root_.IsReduced R')
      (σ : Fin 𝔉.m → SchemeHomOver (𝟙 _) (SmoothProperCurve.baseChange ℚ (cToBase ℚ) R')),
      ∀ (k : Type) [Field k] (ξ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R')),
        Function.Injective (fun j => ξ ≫ (σ j).1) := by
  haveI : IsIntegral (C ℚ) := ThetaSourceComparison.source_integral
  haveI : IsProper (cToBase ℚ) := source_proper
  haveI : IsSeparated (cToBase ℚ) := inferInstance
  exact 𝔉.exists_finiteEtale_geometric_sections
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)))

end FourCorner.ThetaRationalPicardInput
