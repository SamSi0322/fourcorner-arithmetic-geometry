import FourCorner.DenominatorBoundsValuation

set_option autoImplicit false

namespace FourCorner.FiveNormalizeAux

/-- Removing a power of five from a nonzero integer subtracts its exponent
from the finite five-adic valuation. -/
theorem normalize (x : ℤ) (s : ℕ) (hx : x ≠ 0)
    (hs : s ≤ padicValInt 5 x) :
    ∃ a : ℤ, x = (5 : ℤ) ^ s * a ∧ a ≠ 0 ∧
      padicValInt 5 a + s = padicValInt 5 x := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hd : (5 : ℤ) ^ s ∣ x := (padicValInt_dvd_iff s x).mpr (Or.inr hs)
  obtain ⟨a, ha⟩ := hd
  have han : a ≠ 0 := by
    intro h
    apply hx
    simp [ha, h]
  have hp : (5 : ℤ) ^ s ≠ 0 := pow_ne_zero s (by norm_num)
  have hpv : padicValInt 5 ((5 : ℤ) ^ s) = s := by
    rw [padicValInt, Int.natAbs_pow]
    exact padicValNat.prime_pow (p := 5) s
  refine ⟨a, ha, han, ?_⟩
  rw [ha, padicValInt.mul hp han, hpv]
  omega

/-- Dividing out the full five-adic valuation leaves an integer unit at five. -/
theorem normalize_unit (x : ℤ) (hx : x ≠ 0) :
    ∃ a : ℤ, x = (5 : ℤ) ^ padicValInt 5 x * a ∧ a ≠ 0 ∧
      ¬ (5 : ℤ) ∣ a := by
  obtain ⟨a, ha, han, hv⟩ := normalize x (padicValInt 5 x) hx le_rfl
  refine ⟨a, ha, han, ?_⟩
  intro hd
  have hpos := BoundsValuation.padic_pos_of_dvd Nat.prime_five han hd
  omega

end FourCorner.FiveNormalizeAux
