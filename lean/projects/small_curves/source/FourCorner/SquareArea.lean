import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace FourCorner.FermatArea

private structure Triangle (x y z : ℤ) : Prop where
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z
  equation : x ^ 2 + y ^ 2 = z ^ 2
  area : ∃ q : ℚ, (x : ℚ) * y = 2 * q ^ 2

private def Minimal (x y z : ℤ) : Prop :=
  Triangle x y z ∧ ∀ x' y' z' : ℤ, Triangle x' y' z' → z.natAbs ≤ z'.natAbs

private theorem Triangle.symm {x y z : ℤ} (h : Triangle x y z) : Triangle y x z := by
  obtain ⟨q, hq⟩ := h.area
  exact ⟨h.y_pos, h.x_pos, h.z_pos, by nlinarith [h.equation], q, by nlinarith⟩

private theorem Minimal.symm {x y z : ℤ} (h : Minimal x y z) : Minimal y x z :=
  ⟨h.1.symm, h.2⟩

private theorem exists_minimal {x y z : ℤ} (h : Triangle x y z) :
    ∃ x' y' z' : ℤ, Minimal x' y' z' := by
  classical
  let P : ℕ → Prop := fun n => ∃ x' y' z' : ℤ, Triangle x' y' z' ∧ z'.natAbs = n
  have hex : ∃ n, P n := ⟨z.natAbs, x, y, z, h, rfl⟩
  obtain ⟨x', y', z', htri, hsize⟩ := Nat.find_spec hex
  refine ⟨x', y', z', htri, ?_⟩
  intro x'' y'' z'' htri'
  rw [hsize]
  exact Nat.find_min' hex ⟨x'', y'', z'', htri', rfl⟩

private theorem coprime_of_minimal {x y z : ℤ} (h : Minimal x y z) : IsCoprime x y := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hnot
  obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpx' : (p : ℤ) ∣ x := Int.natCast_dvd.mpr hpx
  have hpy' : (p : ℤ) ∣ y := Int.natCast_dvd.mpr hpy
  have ht : PythagoreanTriple x y z := by simpa [PythagoreanTriple, pow_two] using h.1.equation
  have hpz : (p : ℤ) ∣ z := dvd_trans (Int.dvd_coe_gcd hpx' hpy') ht.gcd_dvd
  obtain ⟨x', hx⟩ := hpx'
  obtain ⟨y', hy⟩ := hpy'
  obtain ⟨z', hz⟩ := hpz
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have hpnz : (p : ℤ) ≠ 0 := ne_of_gt hp0
  have hpqnz : (p : ℚ) ≠ 0 := by exact_mod_cast hpnz
  have hnew : Triangle x' y' z' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hh := h.1.x_pos; rw [hx] at hh; nlinarith
    · have hh := h.1.y_pos; rw [hy] at hh; nlinarith
    · have hh := h.1.z_pos; rw [hz] at hh; nlinarith
    · apply (mul_left_inj' (pow_ne_zero 2 hpnz)).mp
      have heq := h.1.equation
      rw [hx, hy, hz] at heq
      linear_combination heq
    · obtain ⟨q, hq⟩ := h.1.area
      refine ⟨q / p, ?_⟩
      rw [hx, hy] at hq
      push_cast at hq
      field_simp
      linear_combination hq
  have hmin := h.2 x' y' z' hnew
  rw [hz, Int.natAbs_mul, Int.natAbs_natCast] at hmin
  have hz' : 0 < z'.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnew.z_pos)
  nlinarith [hp.one_lt]

private theorem exists_odd_minimal {x y z : ℤ} (h : Triangle x y z) :
    ∃ x' y' z' : ℤ, Minimal x' y' z' ∧ x' % 2 = 1 := by
  obtain ⟨x', y', z', hmin⟩ := exists_minimal h
  have ht : PythagoreanTriple x' y' z' := by simpa [PythagoreanTriple, pow_two] using hmin.1.equation
  have hc := Int.isCoprime_iff_gcd_eq_one.mp (coprime_of_minimal hmin)
  rcases ht.even_odd_of_coprime hc with hh | hh
  · exact ⟨y', x', z', hmin.symm, hh.2⟩
  · exact ⟨x', y', z', hmin, hh.1⟩

private theorem positive_square_factor {a b : ℤ} (ha : 0 < a)
    (hc : IsCoprime a b) (hs : IsSquare (a * b)) : ∃ r : ℤ, 0 < r ∧ a = r ^ 2 := by
  obtain ⟨c, hsq⟩ := hs
  obtain ⟨r, hr | hr⟩ := Int.sq_of_isCoprime hc (by simpa only [pow_two] using hsq)
  · refine ⟨|r|, ?_, ?_⟩
    · apply abs_pos.mpr
      intro hz
      simp [hz] at hr
      omega
    · simpa only [sq_abs] using hr
  · nlinarith [sq_nonneg r]

private theorem coprime_sum_difference {m n : ℤ} (hc : IsCoprime m n)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    IsCoprime (m + n) (m - n) := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hnot
  obtain ⟨p, hp, hps, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hps' : (p : ℤ) ∣ m + n := Int.natCast_dvd.mpr hps
  have hpd' : (p : ℤ) ∣ m - n := Int.natCast_dvd.mpr hpd
  have hpm : (p : ℤ) ∣ 2 * m := by
    rw [show 2 * m = (m + n) + (m - n) by ring]
    exact dvd_add hps' hpd'
  have hpn : (p : ℤ) ∣ 2 * n := by
    rw [show 2 * n = (m + n) - (m - n) by ring]
    exact dvd_sub hps' hpd'
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hp2 : p = 2
  · have hs0 := Int.emod_eq_zero_of_dvd hps'
    rw [hp2] at hs0
    have hsmod := Int.add_emod m n 2
    rcases hpar with hh | hh <;> rw [hh.1, hh.2] at hsmod <;> omega
  · have hptwo : ¬ (p : ℤ) ∣ 2 := by
      intro hh
      have hh' : p ∣ 2 := by exact_mod_cast hh
      have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hh'
      have hlow := hp.two_le
      omega
    have hpm' := (hpZ.dvd_or_dvd hpm).resolve_left hptwo
    have hpn' := (hpZ.dvd_or_dvd hpn).resolve_left hptwo
    have hunit := hc.isUnit_of_dvd' hpm' hpn'
    exact hpZ.not_isUnit hunit

private theorem square_mod_two (a : ℤ) : a ^ 2 % 2 = a % 2 := by
  rw [pow_two, Int.mul_emod]
  rcases Int.emod_two_eq_zero_or_one a with h | h <;> rw [h] <;> norm_num

private theorem not_minimal {x y z : ℤ} (h : Minimal x y z) (hxodd : x % 2 = 1) : False := by
  have ht : PythagoreanTriple x y z := by simpa [PythagoreanTriple, pow_two] using h.1.equation
  have hc := Int.isCoprime_iff_gcd_eq_one.mp (coprime_of_minimal h)
  obtain ⟨m, n, hx, hy, hz, hmn, hpar, hmnonneg⟩ :=
    ht.coprime_classification' hc hxodd h.1.z_pos
  have hmpos : 0 < m := by
    by_contra hle
    have hmzero : m = 0 := by omega
    rw [hmzero] at hy
    nlinarith [h.1.y_pos]
  have hnpos : 0 < n := by have hh := h.1.y_pos; rw [hy] at hh; nlinarith
  have hnm : n < m := by have hh := h.1.x_pos; rw [hx] at hh; nlinarith
  have hco : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn
  have hmDiff : IsCoprime m (m ^ 2 - n ^ 2) := by
    have hh : IsCoprime m (-(n ^ 2) + m * m) := hco.pow_right.neg_right.add_mul_right_right m
    convert hh using 1; ring
  have hnDiff : IsCoprime n (m ^ 2 - n ^ 2) := by
    have hh : IsCoprime n (m ^ 2 + (-n) * n) := hco.symm.pow_right.add_mul_right_right (-n)
    convert hh using 1; ring
  have hprod : IsSquare ((m * n) * (m ^ 2 - n ^ 2)) := by
    apply Rat.isSquare_intCast_iff.mp
    obtain ⟨q, hq⟩ := h.1.area
    refine ⟨q, ?_⟩
    rw [hx, hy] at hq
    push_cast at hq ⊢
    linear_combination (1 / 2 : ℚ) * hq
  obtain ⟨r, hrpos, hr⟩ := positive_square_factor (mul_pos hmpos hnpos)
    (hmDiff.mul_left hnDiff) hprod
  obtain ⟨t, htpos, htSq⟩ := positive_square_factor (by nlinarith : 0 < m ^ 2 - n ^ 2)
    (hmDiff.mul_left hnDiff).symm (by simpa only [mul_comm] using hprod)
  have hmnSq : IsSquare (m * n) := ⟨r, by simpa only [pow_two] using hr⟩
  obtain ⟨e, hepos, he⟩ := positive_square_factor hmpos hco hmnSq
  obtain ⟨f, hfpos, hf⟩ := positive_square_factor hnpos hco.symm (by simpa only [mul_comm] using hmnSq)
  have hdiffSq : IsSquare ((m + n) * (m - n)) :=
    ⟨t, by linear_combination htSq⟩
  have hcop := coprime_sum_difference hco hpar
  obtain ⟨k, hkpos, hk⟩ := positive_square_factor (by omega : 0 < m + n) hcop hdiffSq
  obtain ⟨j, hjpos, hj⟩ := positive_square_factor (by omega : 0 < m - n)
    hcop.symm (by simpa only [mul_comm] using hdiffSq)
  have hkj : j < k := by nlinarith
  have hsum : k ^ 2 + j ^ 2 = 2 * e ^ 2 := by nlinarith
  have hmod := congrArg (fun a : ℤ => a % 2) hsum
  have hrhs : 2 * e ^ 2 % 2 = 0 := by rw [Int.mul_emod]; norm_num
  rw [Int.add_emod, square_mod_two, square_mod_two, hrhs] at hmod
  have hke := Int.emod_two_eq_zero_or_one k
  have hje := Int.emod_two_eq_zero_or_one j
  have hsumEven : (2 : ℤ) ∣ k + j := by
    apply Int.dvd_of_emod_eq_zero
    have hh := Int.add_emod k j 2
    omega
  have hdiffEven : (2 : ℤ) ∣ k - j := by
    apply Int.dvd_of_emod_eq_zero
    have hh := Int.sub_emod k j 2
    omega
  obtain ⟨u, hu⟩ := hsumEven
  obtain ⟨v, hv⟩ := hdiffEven
  have huv : 4 * u * v = k ^ 2 - j ^ 2 := by
    calc
      4 * u * v = (2 * u) * (2 * v) := by ring
      _ = (k + j) * (k - j) := by rw [← hu, ← hv]
      _ = k ^ 2 - j ^ 2 := by ring
  have hnew : Triangle u v e := by
    refine ⟨by omega, by omega, hepos, ?_, ?_⟩
    · have huSq := congrArg (fun a : ℤ => a ^ 2) hu
      have hvSq := congrArg (fun a : ℤ => a ^ 2) hv
      nlinarith
    · refine ⟨(f : ℚ) / 2, ?_⟩
      have hh : 2 * u * v = f ^ 2 := by nlinarith
      have hhq : (2 : ℚ) * u * v = (f : ℚ) ^ 2 := by exact_mod_cast hh
      nlinarith
  have hsmall : e.natAbs < z.natAbs := by
    apply Int.ofNat_lt.mp
    rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_pos hepos, abs_of_pos h.1.z_pos]
    nlinarith [Int.le_self_sq e, Int.le_self_sq m, sq_pos_of_ne_zero (ne_of_gt hnpos)]
  exact Nat.not_le_of_lt hsmall (h.2 u v e hnew)

/-- Fermat's square-area theorem, with a rational square root of the area.
The proof is an actual descent on the positive integer hypotenuse. -/
theorem no_rational_square_area (x y z : ℤ) (q : ℚ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (htri : x ^ 2 + y ^ 2 = z ^ 2) (harea : (x : ℚ) * y = 2 * q ^ 2) : False := by
  obtain ⟨x', y', z', hmin, hodd⟩ := exists_odd_minimal ⟨hx, hy, hz, htri, q, harea⟩
  exact not_minimal hmin hodd

#print axioms no_rational_square_area

end FourCorner.FermatArea

namespace FourCorner

/-- A positive rational right triangle cannot have nonzero square area. -/
theorem rational_right_triangle_not_square_area {a b c k : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (htri : a ^ 2 + b ^ 2 = c ^ 2) : a * b / 2 ≠ k ^ 2 := by
  intro harea
  let d : ℚ := a.den * b.den * c.den
  let x : ℤ := a.num * b.den * c.den
  let y : ℤ := b.num * a.den * c.den
  let z : ℤ := c.num * a.den * b.den
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos (mul_pos (by exact_mod_cast a.den_pos) (by exact_mod_cast b.den_pos))
      (by exact_mod_cast c.den_pos)
  have hx : (x : ℚ) = d * a := by
    dsimp [x, d]
    push_cast
    rw [← Rat.mul_den_eq_num a]
    ring
  have hy : (y : ℚ) = d * b := by
    dsimp [y, d]
    push_cast
    rw [← Rat.mul_den_eq_num b]
    ring
  have hz : (z : ℚ) = d * c := by
    dsimp [z, d]
    push_cast
    rw [← Rat.mul_den_eq_num c]
    ring
  have hxpos : 0 < x := by
    have : (0 : ℚ) < x := by rw [hx]; exact mul_pos hd ha
    exact_mod_cast this
  have hypos : 0 < y := by
    have : (0 : ℚ) < y := by rw [hy]; exact mul_pos hd hb
    exact_mod_cast this
  have htriangle : x ^ 2 + y ^ 2 = z ^ 2 := by
    have : (x : ℚ) ^ 2 + (y : ℚ) ^ 2 = (z : ℚ) ^ 2 := by
      rw [hx, hy, hz]
      linear_combination d ^ 2 * htri
    exact_mod_cast this
  have hzpos : 0 < |z| := by
    apply abs_pos.mpr
    intro heq
    rw [heq] at htriangle
    nlinarith [sq_pos_of_pos hxpos, sq_nonneg y]
  apply FermatArea.no_rational_square_area x y |z| (d * k) hxpos hypos hzpos
  · simpa only [sq_abs] using htriangle
  · rw [hx, hy]
    linear_combination 2 * d ^ 2 * harea

#print axioms rational_right_triangle_not_square_area

end FourCorner
