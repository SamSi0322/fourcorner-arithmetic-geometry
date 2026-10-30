import FourCorner.CommonRootRamifiedNecessity
import Mathlib.Tactic
import FourCorner.HasseNormWitness
namespace FourCorner.HasseInertNorm
variable {q : ℕ} [Fact q.Prime]

theorem norm_form_ne_zero (h2 : ¬ IsSquare (2 : ℚ_[q]))
    {a b : ℚ_[q]} (hab : a ≠ 0 ∨ b ≠ 0) : a^2-2*b^2 ≠ 0 := by
  intro he
  by_cases hb : b=0
  · have ha : a=0 := sq_eq_zero_iff.mp (by simpa [hb] using he)
    exact hab.elim (fun h => h ha) (fun h => h hb)
  · apply h2
    refine ⟨a/b, ?_⟩
    field_simp
    linear_combination -he

theorem norm_form_val_equal (hq : q ≠ 2) (h2 : ¬ IsSquare (2 : ℚ_[q]))
    {a b : ℚ_[q]} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : a.valuation=b.valuation) :
    (a^2-2*b^2).valuation=2*a.valuation := by
  have hn := norm_form_ne_zero h2 (Or.inl ha : a ≠ 0 ∨ b ≠ 0)
  have htwo : (2 : ℚ_[q]) ≠ 0 := by norm_num
  have hval : (2*b^2).valuation=2*a.valuation := by
    rw [Padic.valuation_mul htwo (pow_ne_zero _ hb), commonRoot_val_two hq,
      Padic.valuation_pow, heq]
    simp
  have hlo : 2*a.valuation ≤ (a^2-2*b^2).valuation := by
    have hh := Padic.le_valuation_add (x := a^2) (y := -(2*b^2)) (by simpa only [sub_eq_add_neg] using hn)
    rw [commonRoot_val_neg, hval, Padic.valuation_pow] at hh
    simpa [sub_eq_add_neg] using hh
  apply le_antisymm _ hlo
  by_contra hnle
  have hpos : 0 < ((a^2-2*b^2)/b^2).valuation := by
    rw [commonRoot_val_div hn (pow_ne_zero _ hb), Padic.valuation_pow, ← heq]
    omega
  have hsmall : ‖(a^2-2*b^2)/b^2‖ < 1 :=
    (commonRoot_norm_lt_one_iff (div_ne_zero hn (pow_ne_zero _ hb))).mpr hpos
  have hrval : ((a/b)^2).valuation=0 := by
    rw [Padic.valuation_pow, commonRoot_val_div ha hb, heq]
    simp
  have hrnorm : ‖(a/b)^2‖=1 := by
    rw [Padic.norm_eq_zpow_neg_valuation (pow_ne_zero _ (div_ne_zero ha hb)), hrval]
    simp
  apply h2
  apply padic_odd_isSquare_of_norm_sub_lt hq (pow_ne_zero 2 (div_ne_zero ha hb))
    (IsSquare.sq (a/b))
  rw [hrnorm]
  have hid : 2-(a/b)^2 = -((a^2-2*b^2)/b^2) := by field_simp; ring
  simpa [hid] using hsmall

theorem norm_form_val_even (hq : q ≠ 2) (h2 : ¬ IsSquare (2 : ℚ_[q]))
    (a b : ℚ_[q]) : Even (a^2-2*b^2).valuation := by
  by_cases ha : a=0
  · rw [ha]
    by_cases hb : b=0
    · simp [hb]
    · have hv : (0^2-2*b^2).valuation = 2*b.valuation := by
        simp only [zero_pow (by decide : 2 ≠ 0), zero_sub, commonRoot_val_neg]
        rw [Padic.valuation_mul (by norm_num) (pow_ne_zero _ hb), commonRoot_val_two hq,
          Padic.valuation_pow]
        simp
      rw [hv]
      exact even_two_mul _
  by_cases hb : b=0
  · simp only [hb, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, Padic.valuation_pow]
    exact even_two_mul _
  by_cases heq : a.valuation=b.valuation
  · rw [norm_form_val_equal hq h2 ha hb heq]
    exact even_two_mul _
  · have ht : (2*b^2).valuation=2*b.valuation := by
      rw [Padic.valuation_mul (by norm_num) (pow_ne_zero _ hb), commonRoot_val_two hq,
        Padic.valuation_pow]; simp
    have hh := commonRoot_val_sub_of_ne (pow_ne_zero 2 ha)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb))
      (show (a^2).valuation ≠ (2*b^2).valuation by
        rw [Padic.valuation_pow, ht]; omega)
    rw [hh, Padic.valuation_pow, ht]
    rcases le_total a.valuation b.valuation with h | h
    · rw [min_eq_left (by omega)]; exact even_two_mul _
    · rw [min_eq_right (by omega)]; exact even_two_mul _
/-- Norms in the actual quadratic algebra have even valuation at every
odd inert place, including arbitrary positive/negative depths and zero coordinates. -/
theorem algebra_norm_val_even (hq : q ≠ 2) (h2 : ¬ IsSquare (2 : ℚ_[q]))
    (x : HasseNormWitness.SqrtTwo ℚ_[q]) : Even x.norm.valuation := by
  have hh := norm_form_val_even hq h2 x.re x.im
  have he : x.norm=x.re^2-2*x.im^2 := by
    simp only [QuadraticAlgebra.norm_def]; ring
  rwa [he]

/-- Individual p±1 parity is forced by p and their product; negative
valuations are treated explicitly rather than discarded as integral cases. -/
theorem neighbors_even (hq : q ≠ 2) {p : ℚ_[q]}
    (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hep : Even p.valuation) (heab : Even ((p-1)*(p+1)).valuation) :
    Even (p-1).valuation ∧ Even (p+1).valuation := by
  have hsum : Even ((p-1).valuation+(p+1).valuation) := by
    rwa [Padic.valuation_mul ha hb] at heab
  rcases lt_trichotomy (p-1).valuation 0 with hn | hz | hp
  · have hpval : p.valuation=(p-1).valuation := by
      have hh := commonRoot_val_add_of_ne ha (one_ne_zero : (1 : ℚ_[q]) ≠ 0)
        (show (p-1).valuation ≠ (1 : ℚ_[q]).valuation by simpa using ne_of_lt hn)
      simpa only [sub_add_cancel, Padic.valuation_one, min_eq_left (le_of_lt hn)] using hh
    have hbval : (p+1).valuation=(p-1).valuation := by
      have hh := commonRoot_val_add_of_ne ha (by norm_num : (2 : ℚ_[q]) ≠ 0)
        (show (p-1).valuation ≠ (2 : ℚ_[q]).valuation by
          rw [commonRoot_val_two hq]; exact ne_of_lt hn)
      have he : p-1+2=p+1 := by ring
      simpa only [he, commonRoot_val_two hq, min_eq_left (le_of_lt hn)] using hh
    rw [hpval] at hep
    exact ⟨hep, hbval ▸ hep⟩
  · rw [hz, zero_add] at hsum
    exact ⟨hz ▸ (show Even (0 : ℤ) from ⟨0, by simp⟩), hsum⟩
  · have hbval := commonRoot_val_add_one_of_sub_one_pos hq hp
    rw [hbval, add_zero] at hsum
    exact ⟨hsum, hbval ▸ (show Even (0 : ℤ) from ⟨0, by simp⟩)⟩

theorem full_source_inert_valuations (hq : q ≠ 2)
    (h2 : ¬ IsSquare (2 : ℚ_[q]))
    (p Z U V W T : ℚ_[q])
    (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (h0 : ¬ (Z=0 ∧ U=0 ∧ V=0 ∧ W=0 ∧ T=0))
    (hV : p*V^2=2*(p-1)*(U^2-p*Z^2))
    (hW : p*W^2=2*(p+1)*(U^2+p*Z^2))
    (hT : p*T^2=(p-1)*U^2+p*(p+1)*Z^2) :
    Even p.valuation ∧ Even (p-1).valuation ∧ Even (p+1).valuation := by
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := HasseNormWitness.full_source_local_norms
    p Z U V W T hp ha hb h0 hV hW hT
  have hep : Even p.valuation := hx ▸ algebra_norm_val_even hq h2 x
  have heab : Even ((p-1)*(p+1)).valuation := hy ▸ algebra_norm_val_even hq h2 y
  exact ⟨hep, neighbors_even hq ha hb hep heab⟩
#print axioms algebra_norm_val_even
#print axioms neighbors_even
#print axioms full_source_inert_valuations
#print axioms norm_form_val_even
end FourCorner.HasseInertNorm
