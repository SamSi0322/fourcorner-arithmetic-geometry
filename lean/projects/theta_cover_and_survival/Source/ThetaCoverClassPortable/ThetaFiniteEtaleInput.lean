import ThetaCoverClassPortable.FiniteMapEtaleBridge
import ThetaCoverClassPortable.ThetaRationalPicardInput
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels

theorem actual_levelSetsGenericallyEtale
    (𝔉 : SmoothProperCurve.FiniteMapData (cToBase ℚ) OC) (hm : 0 < 𝔉.m) :
    𝔉.LevelSetsGenericallyEtale := by
  haveI : IsIntegral (C ℚ) := ThetaSourceComparison.source_integral
  exact 𝔉.levelSetsGenericallyEtale_of_isUnit
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)))

open scoped TensorProduct

theorem actual_finiteEtale_splitLevelSet
    (𝔉 : SmoothProperCurve.FiniteMapData (cToBase ℚ) OC) (hm : 0 < 𝔉.m) :
    ∃ s : ℚ, Module.Finite ℚ (𝔉.LevelSet s) ∧ Module.Free ℚ (𝔉.LevelSet s) ∧
      Module.finrank ℚ (𝔉.LevelSet s) = 𝔉.m ∧ Algebra.Etale ℚ (𝔉.LevelSet s) ∧
      ∃ (R' : Type) (_ : CommRing R') (_ : Algebra ℚ R') (_ : Module.Finite ℚ R')
        (_ : Algebra.Etale ℚ R') (_ : Module.FaithfullyFlat ℚ R') (_ : IsNoetherianRing R')
        (_ : _root_.IsReduced R'),
        Nonempty ((R' ⊗[ℚ] 𝔉.LevelSet s) ≃ₐ[R'] (Fin 𝔉.m → R')) := by
  haveI : IsIntegral (C ℚ) := ThetaSourceComparison.source_integral
  exact 𝔉.exists_finiteEtale_splitLevelSet
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)))

end FourCorner.ThetaRationalPicardInput
