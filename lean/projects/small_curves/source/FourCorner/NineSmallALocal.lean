import FourCorner.RatIntegralAux
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

set_option maxHeartbeats 6000000

namespace FourCorner.NineSmallA

/-- Possible square residues modulo sixteen, proved by integer congruences. -/
lemma sq_mod_sixteen (x : ℤ) :
    x ^ 2 % 16 = 0 ∨ x ^ 2 % 16 = 1 ∨ x ^ 2 % 16 = 4 ∨ x ^ 2 % 16 = 9 := by
  have h : x ^ 2 % 16 = (x % 16) ^ 2 % 16 := by simp [sq, Int.mul_emod]
  have hlo := Int.emod_nonneg x (by norm_num : (16 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 16)
  interval_cases hx : x % 16 <;> norm_num [hx] at h <;> omega

lemma sq_mod_two (x : ℤ) : x ^ 2 % 2 = x % 2 := by
  have h : x ^ 2 % 2 = (x % 2) ^ 2 % 2 := by simp [sq, Int.mul_emod]
  have hlo := Int.emod_nonneg x (by norm_num : (2 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 2)
  interval_cases hx : x % 2 <;> norm_num [hx] at h ⊢ <;> omega

/-- The twelve unwanted ordered descent rows force every homogeneous
coordinate to be even. This congruence is independent of the height. -/
theorem bad_row_all_even (a c u v z w : ℤ)
    (ha : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 6)
    (hc : c = 1 ∨ c = 2 ∨ c = -1 ∨ c = -2)
    (hbad : ¬ ((a = 1 ∧ c = 1) ∨ (a = 2 ∧ c = 1) ∨
      (a = 3 ∧ c = -2) ∨ (a = 6 ∧ c = -2)))
    (h1 : a * u ^ 2 - (a*c) * v ^ 2 = 6 * w ^ 2)
    (h2 : a * u ^ 2 - c * z ^ 2 = 8 * w ^ 2) :
    2 ∣ u ∧ 2 ∣ v ∧ 2 ∣ z ∧ 2 ∣ w := by
  have su := sq_mod_sixteen u
  have sv := sq_mod_sixteen v
  have sz := sq_mod_sixteen z
  have sw := sq_mod_sixteen w
  have pu := sq_mod_two u
  have pv := sq_mod_two v
  have pz := sq_mod_two z
  have pw := sq_mod_two w
  rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero,
    Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero]
  have hm1 := congrArg (fun t : ℤ => t % 16) h1
  have hm2 := congrArg (fun t : ℤ => t % 16) h2
  clear h1 h2
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl <;> norm_num at hbad
  all_goals
    simp only [Int.sub_emod, Int.mul_emod, Int.emod_emod] at hm1 hm2
    rcases su with su|su|su|su <;> rcases sv with sv|sv|sv|sv <;>
      rcases sw with sw|sw|sw|sw <;> norm_num [su,sv,sw] at hm1
    all_goals
      rcases sz with sz|sz|sz|sz <;> norm_num [su,sz,sw] at hm2 <;> omega

end FourCorner.NineSmallA
#print axioms FourCorner.NineSmallA.bad_row_all_even

namespace FourCorner.NineSmallA

/-- Repeated even divisibility rules out a nonzero homogeneous denominator.
This is a genuine infinite descent, with its decreasing natural measure. -/
theorem homogeneous_descent (a b c : ℤ)
    (hforce : ∀ u v z w : ℤ,
      a*u^2-b*v^2 = 6*w^2 → a*u^2-c*z^2 = 8*w^2 →
      2∣u ∧ 2∣v ∧ 2∣z ∧ 2∣w) :
    ∀ u v z w : ℤ, a*u^2-b*v^2 = 6*w^2 →
      a*u^2-c*z^2 = 8*w^2 → w ≠ 0 → False := by
  have main : ∀ n : ℕ, ∀ u v z w : ℤ, w.natAbs = n →
      a*u^2-b*v^2 = 6*w^2 → a*u^2-c*z^2 = 8*w^2 → w ≠ 0 → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u v z w hn h1 h2 hw
      obtain ⟨⟨u', hu⟩, ⟨v', hv⟩, ⟨z', hz⟩, ⟨w', hw'⟩⟩ := hforce u v z w h1 h2
      have h1' : a*u'^2-b*v'^2 = 6*w'^2 := by
        rw [hu, hv, hw'] at h1
        nlinarith [h1]
      have h2' : a*u'^2-c*z'^2 = 8*w'^2 := by
        rw [hu, hz, hw'] at h2
        nlinarith [h2]
      have hw'0 : w' ≠ 0 := by intro h; apply hw; simp [hw', h]
      have hsm : w'.natAbs < n := by
        rw [hw', Int.natAbs_mul] at hn
        norm_num at hn
        have hp := Int.natAbs_pos.mpr hw'0
        omega
      exact ih _ hsm u' v' z' w' rfl h1' h2' hw'0
  intro u v z w
  exact main w.natAbs u v z w rfl

/-- An inhomogeneous rational solution clears to a nonzero homogeneous
integer denominator; the parity descent therefore applies to rationals. -/
theorem rational_exclusion_of_all_even (a b c : ℤ)
    (hforce : ∀ u v z w : ℤ,
      a*u^2-b*v^2 = 6*w^2 → a*u^2-c*z^2 = 8*w^2 →
      2∣u ∧ 2∣v ∧ 2∣z ∧ 2∣w)
    (u v z : ℚ) (h1 : (a:ℚ)*u^2-(b:ℚ)*v^2 = 6)
    (h2 : (a:ℚ)*u^2-(c:ℚ)*z^2 = 8) : False := by
  let N := u.den * v.den * z.den
  have hN : 0 < N := Nat.mul_pos (Nat.mul_pos u.den_pos v.den_pos) z.den_pos
  have huN : u.den ∣ N := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hvN : v.den ∣ N := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hzN : z.den ∣ N := dvd_mul_left _ _
  obtain ⟨U,hU⟩ := (nat_mul_rat_integral_iff N u).mpr huN
  obtain ⟨V,hV⟩ := (nat_mul_rat_integral_iff N v).mpr hvN
  obtain ⟨Z,hZ⟩ := (nat_mul_rat_integral_iff N z).mpr hzN
  have h1q : (a:ℚ)*(U:ℚ)^2-(b:ℚ)*(V:ℚ)^2 = 6*(N:ℚ)^2 := by
    rw [←hU, ←hV]
    linear_combination (N:ℚ)^2 * h1
  have h2q : (a:ℚ)*(U:ℚ)^2-(c:ℚ)*(Z:ℚ)^2 = 8*(N:ℚ)^2 := by
    rw [←hU, ←hZ]
    linear_combination (N:ℚ)^2 * h2
  exact homogeneous_descent a b c hforce U V Z (N:ℤ)
    (by exact_mod_cast h1q) (by exact_mod_cast h2q) (by exact_mod_cast hN.ne')

/-- Complete rational local classification of the sixteen supported ordered
rows: exactly the four torsion rows survive the dyadic obstruction. -/
theorem rational_row_classification (a c : ℤ) (u v z : ℚ)
    (ha : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 6)
    (hc : c = 1 ∨ c = 2 ∨ c = -1 ∨ c = -2)
    (h1 : (a:ℚ)*u^2-((a*c:ℤ):ℚ)*v^2 = 6)
    (h2 : (a:ℚ)*u^2-(c:ℚ)*z^2 = 8) :
    (a = 1 ∧ c = 1) ∨ (a = 2 ∧ c = 1) ∨
      (a = 3 ∧ c = -2) ∨ (a = 6 ∧ c = -2) := by
  by_contra hbad
  exact rational_exclusion_of_all_even a (a*c) c
    (fun U V Z W => bad_row_all_even a c U V Z W ha hc hbad) u v z h1 h2

end FourCorner.NineSmallA
#print axioms FourCorner.NineSmallA.rational_row_classification
