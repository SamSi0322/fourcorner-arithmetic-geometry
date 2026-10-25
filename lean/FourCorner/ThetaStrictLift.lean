import FourCorner.ThetaMetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Exact rational affine lifting criterion for the quartic quotient.
This file concerns the actual three quadrics and ordered positive metric chart;
no abstract genus or theta-characteristic assertion is assumed. -/
namespace FourCorner

/-- The affine chart Z=1 of the stated plane quartic. -/
def ThetaQuartic (ξ η : ℚ) : Prop :=
  9801 * (ξ^4 + η^4) + 19598 * ξ^2 * η^2 -
    39592 * (ξ^2 + η^2) + 39984 = 0

theorem theta_quartic_elimination {ξ η : ℚ} (h : ThetaQuartic ξ η) :
    (ξ^2 - η^2)^2 + 9800 * (ξ^2 + η^2 - 2)^2 -
      392 * (ξ^2 + η^2 - 2) = 0 := by
  unfold ThetaQuartic at h
  linear_combination h

theorem theta_ellipse {ξ η v w : ℚ} (h : ThetaQuartic ξ η)
    (hv : 2*v^2 = ξ^2 + η^2 - 2) (hv0 : v ≠ 0)
    (hw : 28*w*v = ξ^2 - η^2) : w^2 + 50*v^2 = 1 := by
  have he := theta_quartic_elimination h
  rw [← hv, ← hw] at he
  have hp : (784*v^2) * (w^2 + 50*v^2 - 1) = 0 := by
    linear_combination he
  have hn : (784 : ℚ)*v^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hv0)
  have := (mul_eq_zero.mp hp).resolve_left hn
  linarith

theorem theta_strict_ellipse_iff {v w : ℚ} (hv : 0 < v)
    (he : w^2 + 50*v^2 = 1) :
    (1 + 7*|w| < 50*v) ↔ |w| < 7/11 := by
  have ha : 0 ≤ |w| := abs_nonneg w
  have hs : |w|^2 = w^2 := sq_abs w
  constructor
  · intro h
    have hb : (1+7*|w|)^2 < (50*v)^2 := by nlinarith
    by_contra hn
    have hl : 7/11 ≤ |w| := le_of_not_gt hn
    nlinarith [sq_nonneg (|w| - 7/11)]
  · intro h
    have hp : (11*|w|-7)*(9*|w|+7) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have hb : (1+7*|w|)^2 < (50*v)^2 := by nlinarith
    nlinarith

theorem theta_inverse_source {ξ η v w : ℚ} (h : ThetaQuartic ξ η)
    (hv : 2*v^2 = ξ^2 + η^2 - 2) (hv0 : v ≠ 0)
    (hw : 28*w*v = ξ^2 - η^2) :
    ThetaSource (1/v) (ξ/v) (η/v) (w/v) := by
  have he := theta_ellipse h hv hv0 hw
  have hQ : ξ^2 = w^2 + 14*w*v + 51*v^2 := by linarith
  have hR : η^2 = w^2 - 14*w*v + 51*v^2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination -he
  · field_simp
    linear_combination hQ
  · field_simp
    linear_combination hR

theorem theta_inverse_positive_source {ξ η v w : ℚ} (h : ThetaQuartic ξ η)
    (hξ : 0 < ξ) (hη : 0 < η) (hv : 2*v^2 = ξ^2 + η^2 - 2)
    (hv0 : 0 < v) (hw : 28*w*v = ξ^2 - η^2) (hwlt : |w| < 7/11) :
    ThetaPositiveSource (1/v) (ξ/v) (η/v) (w/v) := by
  have he := theta_ellipse h hv (ne_of_gt hv0) hw
  have hv1 : v < 1 := by nlinarith [sq_nonneg w]
  refine ⟨theta_inverse_source h hv (ne_of_gt hv0) hw, ?_,
    div_pos hξ hv0, div_pos hη hv0, ?_⟩
  · apply (lt_div_iff₀ hv0).mpr
    simpa using hv1
  · rw [abs_div, abs_of_pos hv0]
    have hm := (theta_strict_ellipse_iff hv0 he).mpr hwlt
    have hid : 1/v + 7*(|w|/v) = (1+7*|w|)/v := by ring
    rw [hid]
    exact (div_lt_iff₀ hv0).mpr hm

theorem theta_source_chart {P Q R z : ℚ} (h : ThetaSource P Q R z)
    (hP : P ≠ 0) :
    ThetaQuartic (Q/P) (R/P) ∧
    2*(1/P)^2 = (Q/P)^2 + (R/P)^2 - 2 ∧
    28*(z/P)*(1/P) = (Q/P)^2 - (R/P)^2 ∧
    (z/P)^2 + 50*(1/P)^2 = 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  have hs : 2*(1/P)^2 = (Q/P)^2 + (R/P)^2 - 2 := by
    field_simp
    linear_combination -h₂ - h₃ + 2*h₁
  have hd : 28*(z/P)*(1/P) = (Q/P)^2 - (R/P)^2 := by
    field_simp
    linear_combination -h₂ + h₃
  have he : (z/P)^2 + 50*(1/P)^2 = 1 := by
    field_simp
    linear_combination -h₁
  refine ⟨?_, hs, hd, he⟩
  have heq : ((Q/P)^2 - (R/P)^2)^2 + 9800*((Q/P)^2 + (R/P)^2 - 2)^2 -
      392*((Q/P)^2 + (R/P)^2 - 2) = 0 := by
    rw [← hs, ← hd]
    linear_combination 784*(1/P)^2 * he
  unfold ThetaQuartic
  linear_combination heq

/-- The square root is a positive rational number; its sign is fixed. -/
def ThetaLiftCriterion (ξ η : ℚ) : Prop :=
  0 < ξ ∧ 0 < η ∧ ∃ v : ℚ, 0 < v ∧
    2*v^2 = ξ^2 + η^2 - 2 ∧ |(ξ^2 - η^2)/(28*v)| < 7/11

theorem theta_positive_source_criterion {P Q R z : ℚ}
    (h : ThetaPositiveSource P Q R z) :
    ThetaQuartic (Q/P) (R/P) ∧ ThetaLiftCriterion (Q/P) (R/P) := by
  obtain ⟨hs, hP, hQ, hR, hstrict⟩ := h
  have hp : 0 < P := by linarith
  obtain ⟨hD, hv, hw, he⟩ := theta_source_chart hs (ne_of_gt hp)
  refine ⟨hD, div_pos hQ hp, div_pos hR hp, 1/P, one_div_pos.mpr hp, hv, ?_⟩
  have hwi : ((Q/P)^2 - (R/P)^2)/(28*(1/P)) = z/P := by
    rw [← hw]
    field_simp
  rw [hwi]
  apply (theta_strict_ellipse_iff (one_div_pos.mpr hp) he).mp
  have heq : 1 + 7*|z/P| = (P + 7*|z|)/P := by
    rw [abs_div, abs_of_pos hp]
    field_simp
  rw [heq]
  simpa only [div_eq_mul_inv, one_mul] using div_lt_div_of_pos_right hstrict hp

theorem theta_lift_iff {ξ η : ℚ} (hD : ThetaQuartic ξ η) :
    (∃ P Q R z : ℚ, ThetaPositiveSource P Q R z ∧ Q/P = ξ ∧ R/P = η) ↔
      ThetaLiftCriterion ξ η := by
  constructor
  · rintro ⟨P, Q, R, z, hs, hQ, hR⟩
    have h := (theta_positive_source_criterion hs).2
    rwa [hQ, hR] at h
  · rintro ⟨hξ, hη, v, hv0, hv, hwlt⟩
    let w := (ξ^2-η^2)/(28*v)
    have hw : 28*w*v = ξ^2-η^2 := by dsimp [w]; field_simp
    refine ⟨1/v, ξ/v, η/v, w/v,
      theta_inverse_positive_source hD hξ hη hv hv0 hw hwlt, ?_, ?_⟩
    · field_simp
    · field_simp

/-- The inverse is unique on the positive branch, including its z coordinate. -/
theorem theta_lift_inverse_unique {ξ η v P Q R z : ℚ}
    (hv0 : 0 < v) (hv : 2*v^2 = ξ^2 + η^2 - 2)
    (hs : ThetaPositiveSource P Q R z) (hQ : Q/P = ξ) (hR : R/P = η) :
    P = 1/v ∧ Q = ξ/v ∧ R = η/v ∧ z = ((ξ^2-η^2)/(28*v))/v := by
  have hp : 0 < P := by linarith [hs.2.1]
  have hpne := ne_of_gt hp
  have hvne := ne_of_gt hv0
  obtain ⟨_, hsquare, hdiff, _⟩ := theta_source_chart hs.1 hpne
  rw [hQ, hR] at hsquare hdiff
  have hinv : 1/P = v := by nlinarith [one_div_pos.mpr hp]
  have hP : P = 1/v := by rw [← hinv]; field_simp
  have hQ' : Q = ξ/v := by
    have hh := (div_eq_iff hpne).mp hQ
    rw [hP] at hh
    simpa only [mul_one_div] using hh
  have hR' : R = η/v := by
    have hh := (div_eq_iff hpne).mp hR
    rw [hP] at hh
    simpa only [mul_one_div] using hh
  refine ⟨hP, hQ', hR', ?_⟩
  rw [hinv] at hdiff
  have hz : z/P = (ξ^2-η^2)/(28*v) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hvne)).mpr
    linear_combination hdiff
  have hh := (div_eq_iff hpne).mp hz
  rw [hP] at hh
  simpa only [mul_one_div] using hh

/-- Four rational coordinates in the T=1 chart, without built-in equations. -/
@[ext] structure ThetaAffinePoint where
  P : ℚ
  Q : ℚ
  R : ℚ
  z : ℚ

/-- The fibre predicate uses the literal quadrics and projection ratios. -/
def ThetaStrictFiber (ξ η : ℚ) (t : ThetaAffinePoint) : Prop :=
  ThetaPositiveSource t.P t.Q t.R t.z ∧ t.Q/t.P = ξ ∧ t.R/t.P = η

/-- Full Proposition theta-strict-lift in its rational affine chart. -/
theorem theta_strict_lift_iff_unique {ξ η : ℚ} (hD : ThetaQuartic ξ η) :
    (∃! t : ThetaAffinePoint, ThetaStrictFiber ξ η t) ↔ ThetaLiftCriterion ξ η := by
  constructor
  · rintro ⟨t, ht, _⟩
    exact (theta_lift_iff hD).mp ⟨t.P, t.Q, t.R, t.z, ht⟩
  · intro hc
    obtain ⟨hξ, hη, v, hv0, hv, hwlt⟩ := hc
    let w : ℚ := (ξ^2-η^2)/(28*v)
    have hw : 28*w*v = ξ^2-η^2 := by dsimp [w]; field_simp
    let t : ThetaAffinePoint := ⟨1/v, ξ/v, η/v, w/v⟩
    have ht : ThetaStrictFiber ξ η t := by
      refine ⟨theta_inverse_positive_source hD hξ hη hv hv0 hw hwlt, ?_, ?_⟩
      · change (ξ/v)/(1/v) = ξ
        field_simp
      · change (η/v)/(1/v) = η
        field_simp
    refine ⟨t, ht, ?_⟩
    intro u hu
    obtain ⟨hP, hQ, hR, hz⟩ := theta_lift_inverse_unique hv0 hv hu.1 hu.2.1 hu.2.2
    exact ThetaAffinePoint.ext hP hQ hR hz

/-- The positive root occurring in the criterion has no sign ambiguity. -/
theorem theta_positive_root_unique {ξ η v v' : ℚ}
    (hv : 0 < v) (hv' : 0 < v')
    (hs : 2*v^2 = ξ^2+η^2-2) (hs' : 2*v'^2 = ξ^2+η^2-2) : v = v' := by
  nlinarith

/-- Every lifted fibre point satisfies the original four labelled equations
and the strict open-square inequalities, with opposite difference 1/5. -/
theorem theta_strict_fiber_original {ξ η : ℚ} {t : ThetaAffinePoint}
    (ht : ThetaStrictFiber ξ η t) :
    StrictPoint ((50-t.P-7*t.z)/100) ((50-t.P+7*t.z)/100)
      ((t.P-1)/10) (t.Q/10) (t.R/10) ((t.P+1)/10) ∧
      (t.P+1)/10-(t.P-1)/10 = 1/5 := by
  exact ⟨theta_positive_source_to_strict_point ht.1, theta_opposite_radius_difference t.P⟩

/-- The square-root criterion returns all four original distances at one point. -/
theorem theta_criterion_original {ξ η : ℚ} (hD : ThetaQuartic ξ η)
    (hc : ThetaLiftCriterion ξ η) :
    ∃ t : ThetaAffinePoint, ThetaStrictFiber ξ η t ∧
      StrictPoint ((50-t.P-7*t.z)/100) ((50-t.P+7*t.z)/100)
        ((t.P-1)/10) (t.Q/10) (t.R/10) ((t.P+1)/10) ∧
        (t.P+1)/10-(t.P-1)/10 = 1/5 := by
  obtain ⟨t, ht, _⟩ := (theta_strict_lift_iff_unique hD).mpr hc
  exact ⟨t, ht, theta_strict_fiber_original ht⟩

#print axioms theta_strict_lift_iff_unique
#print axioms theta_positive_root_unique
#print axioms theta_strict_fiber_original
#print axioms theta_criterion_original
#print axioms theta_positive_source_criterion
#print axioms theta_lift_iff
#print axioms theta_lift_inverse_unique
#print axioms theta_inverse_source
#print axioms theta_inverse_positive_source
#print axioms theta_source_chart
#print axioms theta_quartic_elimination
#print axioms theta_ellipse
#print axioms theta_strict_ellipse_iff
end FourCorner
