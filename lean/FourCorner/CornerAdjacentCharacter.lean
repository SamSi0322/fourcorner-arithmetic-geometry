import FourCorner.CornerReciprocityActual

set_option autoImplicit false

namespace FourCorner

private lemma odd_mod_four_eq_of_jacobi_neg_one {u m : ℕ} (hu : Odd u) (hm : Odd m)
    (hchar : jacobiSym (-1) u = (-1 : ℤ) ^ e4 m) : u % 4 = m % 4 := by
  rw [jacobiSym.at_neg_one hu] at hchar
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hu) with hu4 | hu4 <;>
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with hm4 | hm4
  · omega
  · rw [ZMod.χ₄_nat_one_mod_four hu4] at hchar
    norm_num [e4, hm4] at hchar
  · rw [ZMod.χ₄_nat_three_mod_four hu4] at hchar
    norm_num [e4, hm4] at hchar
  · omega

namespace IntegralModel

private lemma adjacent_half_sum_sign (M : IntegralModel) (hX : Odd M.X)
    {i j : Bool × Bool} (hd : cornerDistanceSquared i j = 1)
    (hm : M.cornerClass i % 4 = M.cornerClass j % 4) :
    oddPartChar (M.pairHalfSumNat i j) = (-1 : ℤ) ^ e4 (M.cornerClass i) := by
  have hne : i ≠ j := by
    intro h
    subst j
    simp [cornerDistanceSquared] at hd
  have hLe : Even M.L := even_iff_two_dvd.mpr
    (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  have hmi := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (M.cornerClass_odd hX hLe i))
  have hprod : (M.cornerClass i * M.cornerClass j) % 4 = 1 := by
    rcases hmi with hi | hi <;> rw [Nat.mul_mod, ← hm, hi]
  have hprodE : e4 (M.cornerClass i * M.cornerClass j) = 0 := by
    simp [e4, hprod]
  have he : e4 (M.cornerClass i) = e4 (M.cornerClass j) := by
    unfold e4
    rw [hm]
  have heid : e4 (M.cornerClass i) * e4 (M.cornerClass j) = e4 (M.cornerClass i) := by
    rw [← he]
    unfold e4
    split_ifs <;> norm_num
  simpa only [hd, sub_self, Int.toNat_zero, pow_zero, mul_one, hprodE, add_zero,
    pow_one, heid] using M.actual_pair_reciprocity hX hne

/-- For adjacent corners of the same canonical colour modulo four, the odd
part of their actual positive radius half-sum has that same residue modulo four. -/
theorem adjacent_oddPart_mod_four (M : IntegralModel) (hX : Odd M.X)
    {i j : Bool × Bool} (hd : cornerDistanceSquared i j = 1)
    (hm : M.cornerClass i % 4 = M.cornerClass j % 4) :
    oddPart (M.pairHalfSumNat i j) % 4 = M.cornerClass i % 4 := by
  have hLe : Even M.L := even_iff_two_dvd.mpr
    (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  exact odd_mod_four_eq_of_jacobi_neg_one
    (oddPart_odd (M.pairHalfSumNat_pos i j)) (M.cornerClass_odd hX hLe i)
    (M.adjacent_half_sum_sign hX hd hm)

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.adjacent_oddPart_mod_four
