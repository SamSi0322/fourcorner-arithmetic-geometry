import CrtSupport.CriticalBasicWave24
import CriticalGoodPlacePattern
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option autoImplicit false
namespace FourCorner.CriticalCRTCompletion

/-- The actual Hasse/bad-place existence theorem discharges the prime
pattern input. Small allowed primes use the original exact witnesses. -/
theorem allowed_unit_pattern (p : ℕ) [Fact p.Prime]
    (hmod : p % 4 = 1) (h5 : p ≠ 5) (h13 : p ≠ 13) :
    FourCorner.UnitCriticalSquarePattern p := by
  by_cases hlt : p < 37
  · exact FourCorner.critical_unit_pattern_small Fact.out hmod h5 h13 hlt
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp2)
  obtain ⟨i,hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  have hi2 : i^2 = -1 := by simpa only [pow_two] using hi.symm
  obtain ⟨b,u,v,z,hb,hu,hv,hz,hu2,hv2,hz2⟩ :=
    FourCorner.CriticalGoodPlacePattern.exists_unit_pattern i hi2 h2
      (by simpa only [Nat.card_eq_fintype_card, ZMod.card] using (by omega : 37 ≤ p))
  refine ⟨i,b,1,hi2,hb,?_,?_,?_,?_,one_ne_zero,?_,?_,?_⟩
  · exact ⟨1,by simp⟩
  · exact ⟨u,by simpa only [pow_two] using hu2.symm⟩
  · exact ⟨v,by simpa only [pow_two] using hv2.symm⟩
  · exact ⟨z,by simpa only [pow_two] using hz2.symm⟩
  · rw [← hu2]
    exact pow_ne_zero 2 hu
  · rw [← hv2]
    exact pow_ne_zero 2 hv
  · rw [← hz2]
    exact pow_ne_zero 2 hz

end FourCorner.CriticalCRTCompletion
#print axioms FourCorner.CriticalCRTCompletion.allowed_unit_pattern
