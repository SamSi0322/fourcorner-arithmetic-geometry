import FourCorner.PairSupport
import FourCorner.RamifiedUnits
import FourCorner.SqrtTwoCharacterOne

set_option autoImplicit false

namespace FourCorner

private lemma character_eq_of_sq_eq {p : ℕ} [Fact p.Prime] {a b : ZMod p}
    (hn : quadraticChar (ZMod p) (-1) = 1) (hab : a ^ 2 = b ^ 2) :
    quadraticChar (ZMod p) a = quadraticChar (ZMod p) b := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hab) with h | h
  · rw [h]
  · rw [h, show -b = (-1) * b by ring, map_mul, hn, one_mul]

namespace IntegralModel

private lemma ramified_corner_data (M : IntegralModel) {p : ℕ} [Fact p.Prime]
    {i : Bool × Bool} (hdiv : p ∣ M.cornerClass i) (j : Bool × Bool) :
    (M.L : ZMod p) ≠ 0 ∧ (M.cornerRadius i : ZMod p) = 0 ∧
    (M.cornerRadius j : ZMod p) ^ 2 =
      (cornerDistanceSquared i j : ZMod p) * (M.L : ZMod p) ^ 2 := by
  have hd : (p : ℤ) ∣ M.cornerContent i :=
    Int.natCast_dvd_natCast.mpr (dvd_trans hdiv (squarefreePart_dvd _))
  have hx : (M.cornerX i.1 : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (dvd_trans hd (M.cornerContent_dvd_X i))
  have hy : (M.cornerY i.2 : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (dvd_trans hd (M.cornerContent_dvd_Y i))
  have hL : (M.L : ZMod p) ≠ 0 := by
    intro hz
    have hl : p ∣ M.L.natAbs :=
      Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd M.L p).mp hz)
    exact (Fact.out : p.Prime).ne_one
      (Nat.eq_one_of_dvd_coprimes (M.cornerClass_coprime_side i) hdiv hl)
  have hai := congrArg (fun z : ℤ => (z : ZMod p)) (M.corner_sq i)
  simp only [Int.cast_pow, Int.cast_add, hx, hy, zero_pow (by decide : 2 ≠ 0),
    add_zero, pow_eq_zero_iff (by decide : 2 ≠ 0)] at hai
  have haj := congrArg (fun z : ℤ => (z : ZMod p)) (M.corner_sq j)
  simp only [Int.cast_pow, Int.cast_add] at haj
  have hs := congrArg (fun z : ℤ => (z : ZMod p)) (M.corner_separation_sq i j)
  simp only [Int.cast_pow, Int.cast_add, Int.cast_sub, Int.cast_mul, hx, hy,
    zero_sub, neg_sq] at hs
  exact ⟨hL, hai, haj.trans hs⟩

private lemma ramified_half_sum_character (M : IntegralModel) {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 1) {i : Bool × Bool} (hdiv : p ∣ M.cornerClass i)
    (j : Bool × Bool) :
    legendreSym p ((M.cornerRadius i + M.cornerRadius j) / 2) =
      quadraticChar (ZMod p) (M.cornerRadius j : ZMod p) := by
  obtain ⟨_, hi, _⟩ := M.ramified_corner_data hdiv j
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have h2 : quadraticChar (ZMod p) (2 : ZMod p) = 1 :=
    (quadraticChar_one_iff_isSquare (Ring.two_ne_zero hchar)).mpr
      ((ZMod.exists_sq_eq_two_iff (p := p) (by omega)).mpr (Or.inl hp))
  have he := congrArg (fun z : ℤ => (z : ZMod p)) (M.corner_pair_half_sum_integral i j)
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, hi, zero_add] at he
  have hc := congrArg (quadraticChar (ZMod p)) he
  simpa only [legendreSym, map_mul, h2, one_mul] using hc

private lemma ramified_adjacent_radius_character (M : IntegralModel)
    {p : ℕ} [Fact p.Prime] {i j : Bool × Bool} (hdiv : p ∣ M.cornerClass i)
    (hd : cornerDistanceSquared i j = 1)
    {iota : ZMod p} (hiota : iota ^ 2 = -1)
    (hm : legendreSym p (M.L * M.cornerClass j) = 1) :
    quadraticChar (ZMod p) (M.cornerRadius j : ZMod p) =
      legendreSym p (M.cornerClass j) := by
  obtain ⟨hL, _, hs⟩ := M.ramified_corner_data hdiv j
  have hi0 : iota ≠ 0 := by intro hz; simp [hz] at hiota
  have hn : quadraticChar (ZMod p) (-1) = 1 := by
    rw [← hiota]
    exact quadraticChar_sq_one' hi0
  have heq : (M.cornerRadius j : ZMod p) ^ 2 = (M.L : ZMod p) ^ 2 := by
    simpa only [hd, Int.cast_one, one_mul] using hs
  rw [character_eq_of_sq_eq hn heq]
  have hm' : quadraticChar (ZMod p) (M.L : ZMod p) *
      quadraticChar (ZMod p) (M.cornerClass j : ZMod p) = 1 := by
    simpa only [legendreSym, Int.cast_mul, Int.cast_natCast, map_mul] using hm
  change quadraticChar (ZMod p) (M.L : ZMod p) =
    quadraticChar (ZMod p) ((M.cornerClass j : ℤ) : ZMod p)
  simp only [Int.cast_natCast]
  calc
    _ = quadraticChar (ZMod p) (M.L : ZMod p) * 1 := by ring
    _ = quadraticChar (ZMod p) (M.L : ZMod p) *
        (quadraticChar (ZMod p) (M.L : ZMod p) *
          quadraticChar (ZMod p) (M.cornerClass j : ZMod p)) := by rw [hm']
    _ = _ := by rw [← mul_assoc, ← pow_two, quadraticChar_sq_one hL, one_mul]

private lemma ramified_opposite_radius_character (M : IntegralModel)
    {p : ℕ} [Fact p.Prime] (hp : p % 8 = 1)
    {i j : Bool × Bool} (hdiv : p ∣ M.cornerClass i)
    (hd : cornerDistanceSquared i j = 2)
    {iota : ZMod p} (hiota : iota ^ 2 = -1)
    (hm : legendreSym p (M.L * M.cornerClass j) = quadraticChar (ZMod p) (1 + iota)) :
    quadraticChar (ZMod p) (M.cornerRadius j : ZMod p) =
      legendreSym p (M.cornerClass j) * (-1 : ℤ) ^ ((p - 1) / 8) := by
  obtain ⟨hL, _, hs⟩ := M.ramified_corner_data hdiv j
  have hsqrt : ((M.cornerRadius j : ZMod p) / (M.L : ZMod p)) ^ 2 = 2 := by
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hL)).mpr
    simpa only [hd, Int.cast_ofNat] using hs
  have haeq : (M.cornerRadius j : ZMod p) =
      (M.L : ZMod p) * ((M.cornerRadius j : ZMod p) / (M.L : ZMod p)) := by
    field_simp
  have hm' : quadraticChar (ZMod p) (M.L : ZMod p) *
      quadraticChar (ZMod p) (M.cornerClass j : ZMod p) =
        quadraticChar (ZMod p) (1 + iota) := by
    simpa only [legendreSym, Int.cast_mul, Int.cast_natCast, map_mul] using hm
  rw [haeq, map_mul, sqrt_two_character_one hp hiota hsqrt, ← hm', ← mul_assoc,
    ← mul_assoc, ← pow_two, quadraticChar_sq_one hL, one_mul]
  simp only [legendreSym, Int.cast_natCast]

/-- The split-prime branch of manuscript Lemma `profile-ramified-character`.
The half-sum and both classes come from the original primitive integral model. -/
theorem corner_ramified_character_one (M : IntegralModel) (hX : Odd M.X)
    {p : ℕ} [Fact p.Prime] (hp : p % 8 = 1)
    {i j : Bool × Bool} (hne : i ≠ j) (hdiv : p ∣ M.cornerClass i) :
    legendreSym p ((M.cornerRadius i + M.cornerRadius j) / 2) =
      legendreSym p (M.cornerClass j) *
        ((-1 : ℤ) ^ ((p - 1) / 8)) ^ ((cornerDistanceSquared i j - 1).toNat) := by
  obtain ⟨iota, hiota⟩ := ramified_iota_exists hp
  obtain ⟨hh, hv, ho⟩ := M.ramified_units hX hp hiota i hdiv
  rw [M.ramified_half_sum_character hp hdiv j]
  have hj : j = (!i.1, i.2) ∨ j = (i.1, !i.2) ∨ j = (!i.1, !i.2) := by
    rcases i with ⟨e, f⟩
    rcases j with ⟨g, h⟩
    cases e <;> cases f <;> cases g <;> cases h <;> simp_all
  rcases hj with hj | hj | hj
  · subst j
    have hd : cornerDistanceSquared i (!i.1, i.2) = 1 := by
      rcases i with ⟨e, f⟩
      cases e <;> cases f <;> norm_num [cornerDistanceSquared]
    simpa only [hd, sub_self, Int.toNat_zero, pow_zero, mul_one] using
      M.ramified_adjacent_radius_character hdiv hd hiota hh
  · subst j
    have hd : cornerDistanceSquared i (i.1, !i.2) = 1 := by
      rcases i with ⟨e, f⟩
      cases e <;> cases f <;> norm_num [cornerDistanceSquared]
    simpa only [hd, sub_self, Int.toNat_zero, pow_zero, mul_one] using
      M.ramified_adjacent_radius_character hdiv hd hiota hv
  · subst j
    have hd : cornerDistanceSquared i (!i.1, !i.2) = 2 := by
      rcases i with ⟨e, f⟩
      cases e <;> cases f <;> norm_num [cornerDistanceSquared]
    simpa only [hd, show (2 : ℤ) - 1 = 1 by norm_num, Int.toNat_one, pow_one] using
      M.ramified_opposite_radius_character hp hdiv hd hiota ho

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.corner_ramified_character_one
