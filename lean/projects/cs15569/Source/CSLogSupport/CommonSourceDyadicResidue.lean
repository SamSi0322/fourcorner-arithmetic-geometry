import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace FourCorner

/-- The actual dyadic residue modulo four. -/
def commonSourceResidueFour : ℤ_[2] →+* ZMod 4 := PadicInt.toZModPow 2

/-- Reduction of a residue modulo four to its parity. -/
abbrev commonSourceModFourToTwo : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by decide) (ZMod 2)

/-- Vanishing modulo `2^k` is exactly depth at least `k`, for nonzero dyadic integers. -/
theorem commonSource_residue_zero_iff_depth (a : ℤ_[2]) (ha : a ≠ 0) (k : ℕ) :
    PadicInt.toZModPow k a = 0 ↔ k ≤ a.valuation := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
  exact PadicInt.mem_span_pow_iff_le_valuation a ha k

/-- The parity of the residue modulo four is the direct residue modulo two. -/
theorem commonSource_residue_four_parity (a : ℤ_[2]) :
    commonSourceModFourToTwo (commonSourceResidueFour a) = PadicInt.toZModPow 1 a := by
  simpa only [commonSourceModFourToTwo, commonSourceResidueFour, ZMod.castHom_apply] using
    PadicInt.cast_toZModPow (p := 2) 1 2 (by decide) a

/-- At depth zero the residue modulo four is odd. -/
theorem commonSource_residue_four_of_depth_zero (a : ℤ_[2]) (ha : a ≠ 0)
    (hv : a.valuation = 0) :
    commonSourceResidueFour a = 1 ∨ commonSourceResidueFour a = 3 := by
  have hp : commonSourceModFourToTwo (commonSourceResidueFour a) ≠ 0 := by
    rw [commonSource_residue_four_parity]
    intro hz
    have := (commonSource_residue_zero_iff_depth a ha 1).mp hz
    omega
  have hf : ∀ r : ZMod 4, commonSourceModFourToTwo r ≠ 0 → r = 1 ∨ r = 3 := by
    decide
  exact hf _ hp

/-- At depth one the residue modulo four is exactly two. -/
theorem commonSource_residue_four_of_depth_one (a : ℤ_[2]) (ha : a ≠ 0)
    (hv : a.valuation = 1) : commonSourceResidueFour a = 2 := by
  have hp : commonSourceModFourToTwo (commonSourceResidueFour a) = 0 := by
    rw [commonSource_residue_four_parity]
    exact (commonSource_residue_zero_iff_depth a ha 1).mpr (by omega)
  have hn : commonSourceResidueFour a ≠ 0 := by
    intro hz
    have := (commonSource_residue_zero_iff_depth a ha 2).mp hz
    omega
  have hf : ∀ r : ZMod 4, commonSourceModFourToTwo r = 0 → r ≠ 0 → r = 2 := by
    decide
  exact hf _ hp hn

/-- At every depth at least two the residue modulo four vanishes. -/
theorem commonSource_residue_four_of_depth_ge_two (a : ℤ_[2]) (ha : a ≠ 0)
    (hv : 2 ≤ a.valuation) : commonSourceResidueFour a = 0 :=
  (commonSource_residue_zero_iff_depth a ha 2).mpr hv

/-- Equal finite dyadic depth forces residues modulo four to agree up to sign. -/
theorem commonSource_residue_four_eq_or_neg_of_depth_eq
    (a b : ℤ_[2]) (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : a.valuation = b.valuation) :
    commonSourceResidueFour a = commonSourceResidueFour b ∨
      commonSourceResidueFour a = -commonSourceResidueFour b := by
  rcases lt_trichotomy a.valuation 1 with h0 | h1 | h2
  · have h0a : a.valuation = 0 := by omega
    have h0b : b.valuation = 0 := by omega
    obtain ha4 | ha4 := commonSource_residue_four_of_depth_zero a ha h0a
    <;> obtain hb4 | hb4 := commonSource_residue_four_of_depth_zero b hb h0b
    <;> rw [ha4, hb4]
    <;> decide
  · rw [commonSource_residue_four_of_depth_one a ha h1,
      commonSource_residue_four_of_depth_one b hb (by omega)]
    exact Or.inl rfl
  · rw [commonSource_residue_four_of_depth_ge_two a ha (by omega),
      commonSource_residue_four_of_depth_ge_two b hb (by omega)]
    exact Or.inl rfl

/-- The same assertion with field valuations on integral elements of the actual `ℚ₂`. -/
theorem commonSource_residue_four_eq_or_neg_of_field_depth_eq
    (a b : ℚ_[2]) (ha : a ≠ 0) (hb : b ≠ 0)
    (haint : ‖a‖ ≤ 1) (hbint : ‖b‖ ≤ 1)
    (hv : a.valuation = b.valuation) :
    commonSourceResidueFour ⟨a, haint⟩ = commonSourceResidueFour ⟨b, hbint⟩ ∨
      commonSourceResidueFour ⟨a, haint⟩ = -commonSourceResidueFour ⟨b, hbint⟩ := by
  apply commonSource_residue_four_eq_or_neg_of_depth_eq
  · exact fun h => ha (congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) h)
  · exact fun h => hb (congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) h)
  · exact congrArg Int.toNat hv

#print axioms commonSource_residue_four_eq_or_neg_of_depth_eq
#print axioms commonSource_residue_four_eq_or_neg_of_field_depth_eq

end FourCorner
