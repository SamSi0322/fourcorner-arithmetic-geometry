import ThetaCoverClassPortable.FiniteMapDataBaseChange
import ThetaCoverClassPortable.DFiniteMapData
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
namespace FourCorner.DRationalInputs
open ThetaLiteralModels

/-- The original D/QQ and actual origin, over an arbitrary commutative QQ-algebra. -/
def actual_finiteMapData_baseChange
    (𝔉 : SmoothProperCurve.FiniteMapData toBase OD)
    (T : Type) [CommRing T] [Algebra ℚ T] :
    SmoothProperCurve.FiniteMapData (baseChange ℚ toBase T) (sectionBaseChange T OD) :=
  𝔉.baseChange T

@[simp] theorem actual_finiteMapData_baseChange_m
    (𝔉 : SmoothProperCurve.FiniteMapData toBase OD)
    (T : Type) [CommRing T] [Algebra ℚ T] :
    (actual_finiteMapData_baseChange 𝔉 T).m = 𝔉.m := rfl

/-- Unbounded genuine data on the real base-changed curve, with unit ranks in T itself.
No nonzero, field, domain or locality condition is imposed on T. -/
theorem actual_unbounded_finiteMapData_baseChange (T : Type) [CommRing T] [Algebra ℚ T] :
    ∀ m0 : ℕ, ∃ 𝔊 : SmoothProperCurve.FiniteMapData
      (baseChange ℚ toBase T) (sectionBaseChange T OD),
      m0 ≤ 𝔊.m ∧ IsUnit (𝔊.m : T) := by
  intro m0
  obtain ⟨𝔉, hm, hu⟩ := actual_unbounded_finiteMapData m0
  refine ⟨actual_finiteMapData_baseChange 𝔉 T, hm, ?_⟩
  simpa only [actual_finiteMapData_baseChange_m, map_natCast] using hu.map (algebraMap ℚ T)

end FourCorner.DRationalInputs
