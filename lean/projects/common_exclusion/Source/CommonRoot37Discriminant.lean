import FourCorner.CommonRootPadicResidue
import FourCorner.CriticalSeventeenPadic
import Mathlib.Data.Fintype.Parity

set_option autoImplicit false

namespace FourCorner

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- For the four residue classes in the local test at 37, the discriminant
`t² - 1` is a square in the actual completed field. -/
theorem commonRoot37_discriminant_isSquare {t : ℚ_[37]} (htint : ‖t‖ ≤ 1)
    (ht : padicResidue t htint = 14 ∨ padicResidue t htint = -14 ∨
      padicResidue t htint = 16 ∨ padicResidue t htint = -16) :
    IsSquare (t ^ 2 - 1) := by
  let ti : ℤ_[37] := padicIntegral t htint
  let di : ℤ_[37] := ti ^ 2 - 1
  have hred : PadicInt.toZMod di = 10 ∨ PadicInt.toZMod di = 33 := by
    change PadicInt.toZMod (ti ^ 2 - 1) = 10 ∨
      PadicInt.toZMod (ti ^ 2 - 1) = 33
    simp only [map_sub, map_pow, map_one]
    change padicResidue t htint ^ 2 - 1 = 10 ∨
      padicResidue t htint ^ 2 - 1 = 33
    rcases ht with ht | ht | ht | ht <;> rw [ht] <;> decide
  have hunit : PadicInt.toZMod di ≠ 0 := by
    rcases hred with hred | hred <;> rw [hred] <;> decide
  have hsquare : IsSquare (PadicInt.toZMod di) := by
    rcases hred with hred | hred
    · rw [hred]
      exact ⟨11, by decide⟩
    · rw [hred]
      exact ⟨12, by decide⟩
  have h := (padicInt_isSquare_coe_iff_residue_unit (by decide) di hunit).mpr hsquare
  simpa only [di, ti, PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_one,
    padicIntegral_coe] using h

/-- Two is a nonsquare in the actual 37-adic field, as witnessed by its residue. -/
theorem commonRoot37_two_not_isSquare : ¬ IsSquare (2 : ℚ_[37]) := by
  exact not_isSquare_padic_of_not_isSquare_zmod (p := 37) 2 (by decide)

end FourCorner

#print axioms FourCorner.commonRoot37_discriminant_isSquare
#print axioms FourCorner.commonRoot37_two_not_isSquare
