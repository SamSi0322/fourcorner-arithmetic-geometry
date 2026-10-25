import FourCorner.GaussianCorners
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace FourCorner

/-- A prime congruent to one modulo eight admits a square root of minus one. -/
theorem ramified_iota_exists {p : ℕ} [Fact p.Prime] (hp : p % 8 = 1) :
    ∃ iota : ZMod p, iota ^ 2 = -1 := by
  obtain ⟨iota, hiota⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  exact ⟨iota, by simpa only [pow_two] using hiota.symm⟩

private lemma iota_ne_zero {p : ℕ} [Fact p.Prime] {iota : ZMod p}
    (hiota : iota ^ 2 = -1) : iota ≠ 0 := by
  intro h
  simp [h] at hiota

private lemma quadraticChar_neg_one_of_iota {p : ℕ} [Fact p.Prime] {iota : ZMod p}
    (hiota : iota ^ 2 = -1) : quadraticChar (ZMod p) (-1) = 1 := by
  rw [← hiota]
  exact quadraticChar_sq_one' (iota_ne_zero hiota)

private lemma quadraticChar_iota_of_mod_eight {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 1) {iota : ZMod p} (hiota : iota ^ 2 = -1) :
    quadraticChar (ZMod p) iota = 1 := by
  have hp2 : p ≠ 2 := by omega
  have hchar : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  rw [quadraticChar_eq_pow_of_char_ne_two hchar (iota_ne_zero hiota), ZMod.card]
  have hdiv : p / 2 = 4 * (p / 8) := by omega
  have hi4 : iota ^ 4 = 1 := by
    calc
      iota ^ 4 = (iota ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hiota]; ring
  simp [hdiv, pow_mul, hi4]

private lemma quadraticChar_one_sub_iota {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 1) {iota : ZMod p} (hiota : iota ^ 2 = -1) :
    quadraticChar (ZMod p) (1 - iota) = quadraticChar (ZMod p) (1 + iota) := by
  have heq : (1 - iota) = -iota * (1 + iota) := by
    calc
      1 - iota = -iota - iota ^ 2 := by rw [hiota]; ring
      _ = -iota * (1 + iota) := by ring
  rw [heq, map_mul]
  have hn : quadraticChar (ZMod p) (-iota) = 1 := by
    rw [show -iota = (-1) * iota by ring, map_mul,
      quadraticChar_neg_one_of_iota hiota, quadraticChar_iota_of_mod_eight hp hiota]
    norm_num
  rw [hn, one_mul]

/-- The ramified sign is independent of the chosen square root of minus one. -/
theorem ramified_sign_independent {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 1) {iota jota : ZMod p}
    (hiota : iota ^ 2 = -1) (hjota : jota ^ 2 = -1) :
    quadraticChar (ZMod p) (1 + iota) = quadraticChar (ZMod p) (1 + jota) := by
  have heq : iota = jota ∨ iota = -jota := by
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp (hiota.trans hjota.symm)
  rcases heq with h | h
  · rw [h]
  · rw [h, ← sub_eq_add_neg]
    exact quadraticChar_one_sub_iota hp hjota

private lemma one_add_iota_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 1) {iota : ZMod p} (hiota : iota ^ 2 = -1) :
    1 + iota ≠ 0 := by
  intro h
  have hi : iota = -1 := eq_neg_of_add_eq_zero_right h
  have h1 : (1 : ZMod p) = -1 := by simpa [hi] using hiota
  have h2 : (2 : ZMod p) = 0 := by
    simpa only [one_add_one_eq_two, neg_add_cancel] using
      congrArg (fun z : ZMod p => z + 1) h1
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  exact Ring.two_ne_zero hchar h2

private lemma one_sub_iota_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 1) {iota : ZMod p} (hiota : iota ^ 2 = -1) :
    1 - iota ≠ 0 := by
  simpa only [sub_eq_add_neg] using
    one_add_iota_ne_zero hp (iota := -iota) (by simpa using hiota)

/-- The ramified sign is always one or minus one. -/
theorem ramified_sign_dichotomy {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 1) {iota : ZMod p} (hiota : iota ^ 2 = -1) :
    quadraticChar (ZMod p) (1 + iota) = 1 ∨
      quadraticChar (ZMod p) (1 + iota) = -1 :=
  quadraticChar_dichotomy (one_add_iota_ne_zero hp hiota)


/-- Manuscript equation `int:quartic-sign`, with the integer sign embedded
back into the residue field. -/
theorem ramified_quartic_sign {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 1) {iota : ZMod p} (hiota : iota ^ 2 = -1) :
    (quadraticChar (ZMod p) (1 + iota) : ZMod p) =
      (2 : ZMod p) ^ ((p - 1) / 4) * (-1) ^ ((p - 1) / 8) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  rw [quadraticChar_eq_pow_of_char_ne_two' hchar, ZMod.card]
  have hp2 : p / 2 = 4 * (p / 8) := by omega
  have hp4 : (p - 1) / 4 = 2 * (p / 8) := by omega
  have hp8 : (p - 1) / 8 = p / 8 := by omega
  have hs : (1 + iota) ^ 2 = 2 * iota := by
    calc
      (1 + iota) ^ 2 = 1 + 2 * iota + iota ^ 2 := by ring
      _ = 2 * iota := by rw [hiota]; ring
  have hfour : (1 + iota) ^ 4 = (2 : ZMod p) ^ 2 * (-1) := by
    calc
      (1 + iota) ^ 4 = ((1 + iota) ^ 2) ^ 2 := by ring
      _ = (2 * iota) ^ 2 := by rw [hs]
      _ = (2 : ZMod p) ^ 2 * (-1) := by rw [mul_pow, hiota]
  rw [hp2, hp4, hp8, pow_mul, hfour, mul_pow, pow_mul]


private lemma gaussian_reduction_square {p : ℕ} [Fact p.Prime]
    {a b : ℤ} {m : ℕ} {q : GaussianInt} {iota : ZMod p}
    (hi : iota ^ 2 = -1)
    (hroot : (⟨a, b⟩ : GaussianInt) = (m : GaussianInt) * q ^ 2) :
    (a : ZMod p) + iota * (b : ZMod p) =
      (m : ZMod p) * ((q.re : ZMod p) + iota * (q.im : ZMod p)) ^ 2 := by
  have hre : a = (m : ℤ) * (q.re ^ 2 - q.im ^ 2) := by
    have h := congrArg Zsqrtd.re hroot
    simpa [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul, sub_eq_add_neg, mul_assoc] using h
  have him : b = (m : ℤ) * (2 * q.re * q.im) := by
    have h := congrArg Zsqrtd.im hroot
    simp [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul] at h
    nlinarith
  have hre' : (a : ZMod p) = (m : ZMod p) * ((q.re : ZMod p) ^ 2 - (q.im : ZMod p) ^ 2) := by
    simpa only [Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ZMod p)) hre
  have him' : (b : ZMod p) = (m : ZMod p) * (2 * (q.re : ZMod p) * (q.im : ZMod p)) := by
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ZMod p)) him
  rw [hre', him']
  linear_combination -(m : ZMod p) * (q.im : ZMod p) ^ 2 * hi

private lemma character_of_scaled_square {p : ℕ} [Fact p.Prime]
    {L m q d : ZMod p} (hL : L ≠ 0) (hd : d ≠ 0) (h : m * q ^ 2 = L * d) :
    quadraticChar (ZMod p) (L * m) = quadraticChar (ZMod p) d := by
  have hq : q ≠ 0 := by
    intro hz
    have he : L * d = 0 := by simpa [hz] using h.symm
    exact mul_ne_zero hL hd he
  have hc := congrArg (quadraticChar (ZMod p)) h
  rw [map_mul, map_mul, quadraticChar_sq_one' hq, mul_one] at hc
  rw [map_mul, hc, ← mul_assoc, ← pow_two, quadraticChar_sq_one hL, one_mul]

namespace IntegralModel

private lemma cornerClass_prime_side_nonzero (M : IntegralModel) {p : ℕ}
    [Fact p.Prime] {j : Bool × Bool} (hdiv : p ∣ M.cornerClass j) :
    (M.L : ZMod p) ≠ 0 := by
  intro hz
  have hd : p ∣ M.L.natAbs :=
    Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd M.L p).mp hz)
  exact (Fact.out : p.Prime).ne_one
    (Nat.eq_one_of_dvd_coprimes (M.cornerClass_coprime_side j) hdiv hd)

private lemma cornerClass_prime_coordinates_zero (M : IntegralModel) {p : ℕ}
    [Fact p.Prime] {j : Bool × Bool} (hdiv : p ∣ M.cornerClass j) :
    (M.cornerX j.1 : ZMod p) = 0 ∧ (M.cornerY j.2 : ZMod p) = 0 := by
  have hd : (p : ℤ) ∣ M.cornerContent j :=
    Int.natCast_dvd_natCast.mpr (dvd_trans hdiv (squarefreePart_dvd _))
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
      (dvd_trans hd (M.cornerContent_dvd_X j)),
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
      (dvd_trans hd (M.cornerContent_dvd_Y j))⟩

private lemma corner_character_of_displacement (M : IntegralModel) (hX : Odd M.X)
    {p : ℕ} [Fact p.Prime] {iota : ZMod p} (hi : iota ^ 2 = -1)
    (k : Bool × Bool) {d : ZMod p} (hL : (M.L : ZMod p) ≠ 0) (hd : d ≠ 0)
    (heq : (M.cornerX k.1 : ZMod p) + iota * (M.cornerY k.2 : ZMod p) =
      (M.L : ZMod p) * d) :
    legendreSym p (M.L * M.cornerClass k) = quadraticChar (ZMod p) d := by
  have hLe : Even M.L := even_iff_two_dvd.mpr
    (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  obtain ⟨q, _, hroot, _, _⟩ := M.corner_gaussian_root hX hLe k
  have he := (gaussian_reduction_square hi hroot).symm.trans heq
  simpa only [legendreSym, Int.cast_mul, Int.cast_natCast] using
    character_of_scaled_square hL hd he

/-- The two adjacent corners and the opposite corner obey the ramified unit
restrictions of manuscript Proposition `int:ramified-units`. The multipliers
are the canonical squarefree parts of the actual corner contents. -/
theorem ramified_units (M : IntegralModel) (hX : Odd M.X)
    {p : ℕ} [Fact p.Prime] (hp : p % 8 = 1)
    {iota : ZMod p} (hi : iota ^ 2 = -1)
    (j : Bool × Bool) (hdiv : p ∣ M.cornerClass j) :
    legendreSym p (M.L * M.cornerClass (!j.1, j.2)) = 1 ∧
    legendreSym p (M.L * M.cornerClass (j.1, !j.2)) = 1 ∧
    legendreSym p (M.L * M.cornerClass (!j.1, !j.2)) =
      quadraticChar (ZMod p) (1 + iota) := by
  have hL := M.cornerClass_prime_side_nonzero hdiv
  obtain ⟨hx, hy⟩ := M.cornerClass_prime_coordinates_zero hdiv
  let sx : ZMod p := if j.1 then 1 else -1
  let sy : ZMod p := if j.2 then 1 else -1
  have hx' : (M.cornerX (!j.1) : ZMod p) = (M.L : ZMod p) * sx := by
    dsimp [sx]
    cases he : j.1 <;> simp [cornerX, he] at hx ⊢ <;> linear_combination hx
  have hy' : (M.cornerY (!j.2) : ZMod p) = (M.L : ZMod p) * sy := by
    dsimp [sy]
    cases he : j.2 <;> simp [cornerY, he] at hy ⊢ <;> linear_combination hy
  have hsx : sx ≠ 0 := by dsimp [sx]; split <;> norm_num
  have hsy : sy ≠ 0 := by dsimp [sy]; split <;> norm_num
  have hcx : quadraticChar (ZMod p) sx = 1 := by
    dsimp [sx]; split
    · exact map_one _
    · exact quadraticChar_neg_one_of_iota hi
  have hcy : quadraticChar (ZMod p) sy = 1 := by
    dsimp [sy]; split
    · exact map_one _
    · exact quadraticChar_neg_one_of_iota hi
  have hhor := M.corner_character_of_displacement hX hi (!j.1, j.2) hL hsx
    (by simpa only [hy, mul_zero, add_zero] using hx')
  have hver := M.corner_character_of_displacement hX hi (j.1, !j.2) hL
    (mul_ne_zero (iota_ne_zero hi) hsy) (by rw [hx, hy']; ring)
  have hdc : quadraticChar (ZMod p) (sx + iota * sy) =
      quadraticChar (ZMod p) (1 + iota) := by
    dsimp [sx, sy]
    cases j.1 <;> cases j.2 <;> simp only [Bool.false_eq_true, ↓reduceIte,
      mul_neg_one, mul_one]
    · rw [show (-1 : ZMod p) + -iota = (-1) * (1 + iota) by ring,
        map_mul, quadraticChar_neg_one_of_iota hi, one_mul]
    · rw [show (-1 : ZMod p) + iota = (-1) * (1 - iota) by ring,
        map_mul, quadraticChar_neg_one_of_iota hi, one_mul,
        quadraticChar_one_sub_iota hp hi]
    · simpa only [sub_eq_add_neg] using quadraticChar_one_sub_iota hp hi
  have hd : sx + iota * sy ≠ 0 := by
    intro hz
    have : quadraticChar (ZMod p) (1 + iota) = 0 := by
      rw [← hdc, hz, quadraticChar_zero]
    exact one_add_iota_ne_zero hp hi (quadraticChar_eq_zero_iff.mp this)
  have hopp := M.corner_character_of_displacement hX hi (!j.1, !j.2) hL hd
    (by rw [hx', hy']; ring)
  refine ⟨hhor.trans hcx, ?_, hopp.trans hdc⟩
  rw [hver, map_mul, quadraticChar_iota_of_mod_eight hp hi, hcy, mul_one]

end IntegralModel
end FourCorner

#print axioms FourCorner.ramified_sign_independent
#print axioms FourCorner.ramified_sign_dichotomy
#print axioms FourCorner.IntegralModel.ramified_units

#print axioms FourCorner.ramified_iota_exists

#print axioms FourCorner.ramified_quartic_sign
