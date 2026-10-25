import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Conditional group-theoretic completion of the uniform torsion argument

These lemmas concern arbitrary additive commutative groups. They do not assert
any of the curve-specific inputs: absence of odd torsion, the two-torsion kernel,
and the obstruction to an element of order eight must be proved separately.
-/

namespace FourCorner.UniformTorsion

variable {G : Type*} [AddCommGroup G]

/-- Every positive divisor of a finite additive order occurs as the order of a
multiple of the original point. -/
theorem finite_order_divisor_point {P : G} (hP : IsOfFinAddOrder P)
    {n : ℕ} (hn : n ∣ addOrderOf P) :
    addOrderOf ((addOrderOf P / n) • P) = n := by
  have hP0 : addOrderOf P ≠ 0 := hP.addOrderOf_pos.ne'
  have hq0 : addOrderOf P / n ≠ 0 := by
    intro hq
    have hmul := Nat.div_mul_cancel hn
    rw [hq, zero_mul] at hmul
    exact hP0 hmul.symm
  rw [addOrderOf_nsmul_of_dvd hq0 (Nat.div_dvd_of_dvd hn),
    Nat.div_div_self hn hP0]

/-- Absence of odd torsion forces every finite additive order to be a power of
 two. The argument extracts a point of order equal to an odd prime divisor. -/
theorem finite_order_is_two_power
    (hodd : ∀ (n : ℕ), Odd n → ∀ P : G, n • P = 0 → P = 0)
    {P : G} (hP : IsOfFinAddOrder P) : ∃ k : ℕ, addOrderOf P = 2 ^ k := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (addOrderOf P) with h | h
  · exact h
  · rcases h with ⟨p, hp, hpd, hpo⟩
    let Q : G := (addOrderOf P / p) • P
    have hQ : addOrderOf Q = p := finite_order_divisor_point hP hpd
    have hkill : p • Q = 0 := by
      rw [← hQ]
      exact addOrderOf_nsmul_eq_zero Q
    have hzero : Q = 0 := hodd p hpo Q hkill
    have hpone : p = 1 := by simpa [hzero] using hQ.symm
    exact (hp.ne_one hpone).elim

/-- The elementary finite-order reduction. Its two inputs are genuine lower
facts, rather than a hypothesis asserting the desired four-point classification. -/
theorem four_nsmul_eq_zero_of_no_odd_no_eight
    (hodd : ∀ (n : ℕ), Odd n → ∀ P : G, n • P = 0 → P = 0)
    (height : ∀ P : G, addOrderOf P ≠ 8)
    {P : G} (hP : IsOfFinAddOrder P) : 4 • P = 0 := by
  obtain ⟨k, hk⟩ := finite_order_is_two_power hodd hP
  have hklt : k < 3 := by
    by_contra h
    have hd : 8 ∣ addOrderOf P := by
      rw [hk]
      exact Nat.pow_dvd_pow 2 (show 3 ≤ k by omega)
    exact height _ (finite_order_divisor_point hP hd)
  apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
  rw [hk]
  exact Nat.pow_dvd_pow 2 (show k ≤ 2 by omega)

/-- Once four annihilates a point, the two-torsion kernel identifies it as one
of the visible points `0`, `2 • T`, `T`, or `-T`. -/
theorem four_torsion_classification (T : G) (hT : 4 • T = 0)
    (hker : ∀ Q : G, 2 • Q = 0 → Q = 0 ∨ Q = 2 • T)
    {P : G} (hP : 4 • P = 0) :
    P = 0 ∨ P = 2 • T ∨ P = T ∨ P = -T := by
  have hdouble : 2 • (2 • P) = 0 := by simpa [← mul_nsmul] using hP
  rcases hker (2 • P) hdouble with hz | hs
  · rcases hker P hz with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hsub : 2 • (P - T) = 0 := by rw [nsmul_sub, hs, sub_self]
    rcases hker (P - T) hsub with hz | hs
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp hz)))
    · right; right; right
      apply eq_neg_iff_add_eq_zero.mpr
      have hPT : P = 2 • T + T := sub_eq_iff_eq_add.mp hs
      rw [hPT]
      convert hT using 1
      simp only [show (4 : ℕ) = 2 + 2 by rfl, add_nsmul, two_nsmul]
      abel

/-- A nonzero element of order eight has a nonzero fourth multiple in the
 two-torsion kernel. Thus the absence of a fourth root of `2 • T` excludes it. -/
theorem no_order_eight_of_no_fourth_root (T : G)
    (hker : ∀ Q : G, 2 • Q = 0 → Q = 0 ∨ Q = 2 • T)
    (hroot : ∀ P : G, 4 • P ≠ 2 • T) : ∀ P : G, addOrderOf P ≠ 8 := by
  intro P hP
  have h8 : 8 • P = 0 := by
    rw [← hP]
    exact addOrderOf_nsmul_eq_zero P
  have h4 : 4 • P ≠ 0 := by
    intro hz
    have hle := addOrderOf_le_of_nsmul_eq_zero (by norm_num : 0 < 4) hz
    omega
  have h2 : 2 • (4 • P) = 0 := by simpa [← mul_nsmul] using h8
  exact hroot P ((hker (4 • P) h2).resolve_left h4)

/-- It also suffices to prove that the visible order-four point has no half.
The possible half of `-T` is ruled out by negating it. -/
theorem no_order_eight_of_no_half (T : G) (hT : 4 • T = 0)
    (hker : ∀ Q : G, 2 • Q = 0 → Q = 0 ∨ Q = 2 • T)
    (hhalf : ∀ P : G, 2 • P ≠ T) : ∀ P : G, addOrderOf P ≠ 8 := by
  intro P hP
  have h8 : 8 • P = 0 := by
    rw [← hP]
    exact addOrderOf_nsmul_eq_zero P
  have h4 : 4 • P ≠ 0 := by
    intro hz
    have hle := addOrderOf_le_of_nsmul_eq_zero (by norm_num : 0 < 4) hz
    omega
  have h2 : 4 • (2 • P) = 0 := by simpa [← mul_nsmul] using h8
  rcases four_torsion_classification T hT hker h2 with hz | hs | ht | ht
  · apply h4
    calc 4 • P = 2 • (2 • P) := by simp [← mul_nsmul]
         _ = 0 := by rw [hz, smul_zero]
  · apply h4
    calc 4 • P = 2 • (2 • P) := by simp [← mul_nsmul]
         _ = 2 • (2 • T) := by rw [hs]
         _ = 0 := by simpa [← mul_nsmul] using hT
  · exact hhalf P ht
  · apply hhalf (-P)
    rw [smul_neg, ht, neg_neg]

/-- A conditional four-point classification of all finite-order elements. -/
theorem finite_torsion_classification (T : G) (hT : 4 • T = 0)
    (hodd : ∀ (n : ℕ), Odd n → ∀ P : G, n • P = 0 → P = 0)
    (height : ∀ P : G, addOrderOf P ≠ 8)
    (hker : ∀ Q : G, 2 • Q = 0 → Q = 0 ∨ Q = 2 • T)
    {P : G} (hP : IsOfFinAddOrder P) :
    P = 0 ∨ P = 2 • T ∨ P = T ∨ P = -T :=
  four_torsion_classification T hT hker
    (four_nsmul_eq_zero_of_no_odd_no_eight hodd height hP)

/-- The same group completion with a fourth-root obstruction as its input. -/
theorem finite_torsion_classification_of_no_fourth_root (T : G) (hT : 4 • T = 0)
    (hodd : ∀ (n : ℕ), Odd n → ∀ P : G, n • P = 0 → P = 0)
    (hker : ∀ Q : G, 2 • Q = 0 → Q = 0 ∨ Q = 2 • T)
    (hroot : ∀ P : G, 4 • P ≠ 2 • T)
    {P : G} (hP : IsOfFinAddOrder P) :
    P = 0 ∨ P = 2 • T ∨ P = T ∨ P = -T :=
  finite_torsion_classification T hT hodd
    (no_order_eight_of_no_fourth_root T hker hroot) hker hP

/-- The conditional completion using an obstruction to halving the visible
order-four point, as supplied for example by the duplication abscissa. -/
theorem finite_torsion_classification_of_no_half (T : G) (hT : 4 • T = 0)
    (hodd : ∀ (n : ℕ), Odd n → ∀ P : G, n • P = 0 → P = 0)
    (hker : ∀ Q : G, 2 • Q = 0 → Q = 0 ∨ Q = 2 • T)
    (hhalf : ∀ P : G, 2 • P ≠ T)
    {P : G} (hP : IsOfFinAddOrder P) :
    P = 0 ∨ P = 2 • T ∨ P = T ∨ P = -T :=
  finite_torsion_classification T hT hodd
    (no_order_eight_of_no_half T hT hker hhalf) hker hP

#print axioms finite_order_divisor_point
#print axioms finite_order_is_two_power
#print axioms four_nsmul_eq_zero_of_no_odd_no_eight
#print axioms four_torsion_classification
#print axioms no_order_eight_of_no_fourth_root
#print axioms no_order_eight_of_no_half
#print axioms finite_torsion_classification
#print axioms finite_torsion_classification_of_no_fourth_root
#print axioms finite_torsion_classification_of_no_half

end FourCorner.UniformTorsion
