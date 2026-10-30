import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace AlgebraicCurve.HasseWeil

/-- A multiset of roots on a circle bounds each power sum, with multiplicity. -/
theorem norm_sum_pow_le_card_mul (s : Multiset ℂ) (R : ℝ) (n : ℕ) :
    (∀ z ∈ s, ‖z‖ = R) →
      ‖(s.map (fun z => z ^ n)).sum‖ ≤ (s.card : ℝ) * R ^ n := by
  induction s using Multiset.induction_on with
  | empty =>
      intro _
      simp
  | @cons a s ih =>
      intro h
      have ha : ‖a‖ = R := h a (by simp)
      have hs : ∀ z ∈ s, ‖z‖ = R := fun z hz => h z (by simp [hz])
      calc
        ‖((a ::ₘ s).map (fun z => z ^ n)).sum‖ =
            ‖a ^ n + (s.map (fun z => z ^ n)).sum‖ := by simp
        _ ≤ ‖a ^ n‖ + ‖(s.map (fun z => z ^ n)).sum‖ := norm_add_le _ _
        _ ≤ R ^ n + (s.card : ℝ) * R ^ n := by
          rw [norm_pow, ha]
          exact add_le_add le_rfl (ih hs)
        _ = ((a ::ₘ s).card : ℝ) * R ^ n := by
          simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- The sharp numerical bound follows from the polynomial degree, root norms,
and the trace formula. This lemma has no curve-theoretic dependencies. -/
theorem point_bound_of_root_data
    (q g N n : ℕ) (P : Polynomial ℤ)
    (hPm : P.Monic) (hdeg : P.natDegree = 2 * g)
    (hroot : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z‖ = Real.sqrt (q : ℝ))
    (hcount : (N : ℂ) = (q : ℂ) ^ n + 1 -
      (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum)) :
    |(N : ℝ) - ((q : ℝ) ^ n + 1)| ≤ 2 * (g : ℝ) * Real.sqrt (q : ℝ) ^ n := by
  have hcard : (P.map (Int.castRingHom ℂ)).roots.card = 2 * g := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hPm.natDegree_map, hdeg]
  have hsum := norm_sum_pow_le_card_mul
    (P.map (Int.castRingHom ℂ)).roots (Real.sqrt (q : ℝ)) n hroot
  rw [hcard] at hsum
  have heq : (((N : ℝ) - ((q : ℝ) ^ n + 1) : ℝ) : ℂ) =
      -(((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum) := by
    push_cast
    linear_combination hcount
  have hnorm : |(N : ℝ) - ((q : ℝ) ^ n + 1)| =
      ‖((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, heq, norm_neg]
  rw [hnorm]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsum

end AlgebraicCurve.HasseWeil
