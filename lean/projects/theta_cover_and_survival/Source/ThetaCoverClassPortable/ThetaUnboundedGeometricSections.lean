import ThetaCoverClassPortable.ThetaActualGeometricSections
import ThetaCoverClassPortable.ThetaFiniteMapData
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels

/-- Unconditionally arbitrarily many distinct geometric sections, over an
actual finite faithfully flat etale Q-algebra, on the ORIGINAL curve. -/
theorem actual_unbounded_geometric_sections (m0 : ℕ) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra ℚ R') (_ : Module.Finite ℚ R')
      (_ : Algebra.Etale ℚ R') (_ : Module.FaithfullyFlat ℚ R') (_ : IsNoetherianRing R')
      (_ : _root_.IsReduced R') (N : ℕ) (_ : m0 < N)
      (σ : Fin N → SchemeHomOver (𝟙 _) (SmoothProperCurve.baseChange ℚ (cToBase ℚ) R')),
      ∀ (k : Type) [Field k] (ξ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R')),
        Function.Injective (fun j => ξ ≫ (σ j).1) := by
  let 𝔉 := actual_finiteMapData m0
  have hm : m0 < 𝔉.m := actual_finiteMapData_rank_gt m0
  have hpos : 0 < 𝔉.m := lt_of_le_of_lt (Nat.zero_le m0) hm
  obtain ⟨R', _, _, _, _, _, _, _, σ, hσ⟩ := actual_exists_finiteEtale_geometric_sections 𝔉 hpos
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 𝔉.m, hm, σ, hσ⟩

end FourCorner.ThetaRationalPicardInput
