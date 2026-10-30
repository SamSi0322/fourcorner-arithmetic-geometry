import ThetaCoverClassPortable.DFiniteMapData
import ThetaCoverClassPortable.DGeometricGenus
import ThetaCoverClassPortable.DBaseChangeFields
import ThetaCoverClassPortable.DRationalModel
import ThetaCoverClassPortable.DGeometricNativeModel
import ThetaCoverClassPortable.ThetaCoverRationalData
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
namespace FourCorner.DRationalInputs

/-- Matches the point used by the frozen cover-class/Cartier packets. -/
theorem OD_val_eq_cover_origin : OD.1 = ThetaCoverRationalData.rationalPoint (true,true) :=
  ThetaCoverRationalData.rational_origin_preserved.symm

def coverOrigin : NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of ℚ))) toBase :=
  ⟨ThetaCoverRationalData.rationalPoint (true,true), ThetaCoverRationalData.rationalPoint_over _⟩

theorem OD_eq_coverOrigin : OD = coverOrigin := Subtype.ext OD_val_eq_cover_origin

/-- Original generic finite-map-input spelling, on D and OD themselves. -/
theorem actual_hF : ∀ m0 : ℕ, ∃ F : SmoothProperCurve.FiniteMapData toBase OD, m0 ≤ F.m := by
  intro m0
  obtain ⟨F,hF,_⟩ := actual_unbounded_finiteMapData m0
  exact ⟨F,hF⟩

/-- The genuine finite-map datum has the exact single-OD complement. -/
theorem actual_finiteMapData_U (m0 : ℕ) : (actual_finiteMapData m0).U = originComplement :=
  (actual_native_singlePole_charts m0).U_eq_originComplement

end FourCorner.DRationalInputs
