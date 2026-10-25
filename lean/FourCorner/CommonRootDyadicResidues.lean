import FourCorner.CommonRootDyadicFinite
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

set_option autoImplicit false

namespace FourCorner

private instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The completed dyadic integer lies in `2^k ℤ₂` exactly when its actual
reduction modulo `2^k` vanishes. -/
theorem dyadic_residue_zero_iff_norm_le (a : ℤ_[2]) (k : ℕ) :
    PadicInt.toZModPow k a = 0 ↔ ‖a‖ ≤ (2 : ℝ)^(-(k : ℤ)) := by
  have h := PadicInt.norm_le_pow_iff_mem_span_pow a k
  norm_num only [Nat.cast_ofNat] at h
  have hk := PadicInt.ker_toZModPow (p := 2) k
  norm_num only [Nat.cast_ofNat] at hk
  rw [h, ← hk, RingHom.mem_ker]

/-- Unit detection in the genuine completed dyadic ring. -/
theorem dyadic_norm_one_iff_residue_ne_zero (a : ℤ_[2]) :
    ‖a‖ = 1 ↔ PadicInt.toZModPow 1 a ≠ 0 := by
  have hz := dyadic_residue_zero_iff_norm_le a 1
  have hd := PadicInt.norm_le_pow_iff_norm_lt_pow_add_one a (-1)
  norm_num at hz hd
  constructor
  · intro h hzero
    have := hz.mp hzero
    rw [h] at this
    norm_num at this
  · intro h
    apply le_antisymm (PadicInt.norm_le_one a)
    by_contra hh
    have hlt : ‖a‖ < 1 := lt_of_not_ge hh
    exact h (hz.mpr (hd.mpr hlt))

/-- Divisibility by four, retaining all valuation depths including zero. -/
theorem dyadic_residue_four_zero_iff_norm (a : ℤ_[2]) :
    PadicInt.toZModPow 2 a = 0 ↔ ‖a‖ ≤ (1 : ℝ)/4 := by
  simpa using (dyadic_residue_zero_iff_norm_le a 2) |>.trans (by norm_num)

private theorem dyadic_cast_mod_two (a : ℤ_[2]) :
    dyadicMod8ToMod2 (PadicInt.toZModPow 3 a) = PadicInt.toZModPow 1 a := by
  simpa only [dyadicMod8ToMod2, ZMod.castHom_apply] using
    PadicInt.cast_toZModPow (p := 2) 1 3 (by decide) a

private theorem dyadic_cast_mod_four (a : ℤ_[2]) :
    dyadicMod8ToMod4 (PadicInt.toZModPow 3 a) = PadicInt.toZModPow 2 a := by
  simpa only [dyadicMod8ToMod4, ZMod.castHom_apply] using
    PadicInt.cast_toZModPow (p := 2) 2 3 (by decide) a

/-- The primitive integral dyadic four-square system has side divisible by
four, exactly one unit coordinate, the other coordinate divisible by four,
and four unit square roots. This is an assertion in the actual completed ring,
not merely a residue-class necessary condition. -/
theorem common_root_dyadic_primitive_norms
    (N X Y A0 A1 A2 A3 : ℤ_[2])
    (h0 : A0^2 = X^2 + Y^2)
    (h1 : A1^2 = (N-X)^2 + Y^2)
    (h2 : A2^2 = X^2 + (N-Y)^2)
    (h3 : A3^2 = (N-X)^2 + (N-Y)^2)
    (hprim : ‖N‖ = 1 ∨ ‖X‖ = 1 ∨ ‖Y‖ = 1) :
    ‖N‖ ≤ (1 : ℝ)/4 ∧
    ((‖X‖ = 1 ∧ ‖Y‖ ≤ (1 : ℝ)/4) ∨
      (‖X‖ ≤ (1 : ℝ)/4 ∧ ‖Y‖ = 1)) ∧
    ‖A0‖ = 1 ∧ ‖A1‖ = 1 ∧ ‖A2‖ = 1 ∧ ‖A3‖ = 1 := by
  let r : ℤ_[2] →+* ZMod 8 := PadicInt.toZModPow 3
  have h0r : (r A0)^2 = (r X)^2 + (r Y)^2 := by
    simpa only [map_pow, map_add] using congrArg r h0
  have h1r : (r A1)^2 = (r N-r X)^2 + (r Y)^2 := by
    simpa only [map_pow, map_add, map_sub] using congrArg r h1
  have h2r : (r A2)^2 = (r X)^2 + (r N-r Y)^2 := by
    simpa only [map_pow, map_add, map_sub] using congrArg r h2
  have h3r : (r A3)^2 = (r N-r X)^2 + (r N-r Y)^2 := by
    simpa only [map_pow, map_add, map_sub] using congrArg r h3
  have hc2 (a : ℤ_[2]) : dyadicMod8ToMod2 (r a) = PadicInt.toZModPow 1 a :=
    dyadic_cast_mod_two a
  have hc4 (a : ℤ_[2]) : dyadicMod8ToMod4 (r a) = PadicInt.toZModPow 2 a :=
    dyadic_cast_mod_four a
  have hp : dyadicMod8ToMod2 (r N) ≠ 0 ∨ dyadicMod8ToMod2 (r X) ≠ 0 ∨
      dyadicMod8ToMod2 (r Y) ≠ 0 := by
    rw [hc2 N, hc2 X, hc2 Y]
    rcases hprim with hN | hX | hY
    · exact Or.inl ((dyadic_norm_one_iff_residue_ne_zero N).mp hN)
    · exact Or.inr (Or.inl ((dyadic_norm_one_iff_residue_ne_zero X).mp hX))
    · exact Or.inr (Or.inr ((dyadic_norm_one_iff_residue_ne_zero Y).mp hY))
  have hsq (a b : ZMod 8) (h : a^2=b) : IsSquare b := by
    exact ⟨a, by simpa only [pow_two] using h.symm⟩
  obtain ⟨hN, hXY, hA0, hA1, hA2, hA3⟩ :=
    common_root_dyadic_finite (hsq _ _ h0r) (hsq _ _ h1r)
      (hsq _ _ h2r) (hsq _ _ h3r) hp
  have hN' : ‖N‖ ≤ (1 : ℝ)/4 := by
    apply (dyadic_residue_four_zero_iff_norm N).mp
    rwa [hc4 N] at hN
  have hXY' : (‖X‖ = 1 ∧ ‖Y‖ ≤ (1 : ℝ)/4) ∨
      (‖X‖ ≤ (1 : ℝ)/4 ∧ ‖Y‖ = 1) := by
    rw [hc2 X, hc4 Y, hc4 X, hc2 Y] at hXY
    rcases hXY with ⟨hX, hY⟩ | ⟨hX, hY⟩
    · exact Or.inl ⟨(dyadic_norm_one_iff_residue_ne_zero X).mpr hX,
        (dyadic_residue_four_zero_iff_norm Y).mp hY⟩
    · exact Or.inr ⟨(dyadic_residue_four_zero_iff_norm X).mp hX,
        (dyadic_norm_one_iff_residue_ne_zero Y).mpr hY⟩
  have hunit (a : ℤ_[2]) (h : dyadicMod8ToMod2 ((r a)^2) ≠ 0) : ‖a‖ = 1 := by
    apply (dyadic_norm_one_iff_residue_ne_zero a).mpr
    intro hz
    apply h
    rw [map_pow]
    change (dyadicMod8ToMod2 (PadicInt.toZModPow 3 a))^2 = 0
    rw [dyadic_cast_mod_two, hz, zero_pow (by decide : 2 ≠ 0)]
  exact ⟨hN', hXY', hunit A0 (h0r ▸ hA0), hunit A1 (h1r ▸ hA1),
    hunit A2 (h2r ▸ hA2), hunit A3 (h3r ▸ hA3)⟩

end FourCorner

#print axioms FourCorner.dyadic_residue_zero_iff_norm_le
#print axioms FourCorner.dyadic_norm_one_iff_residue_ne_zero
#print axioms FourCorner.dyadic_residue_four_zero_iff_norm
#print axioms FourCorner.common_root_dyadic_primitive_norms
