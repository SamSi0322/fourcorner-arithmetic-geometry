import UniformCurve
import UniformDyadic
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Data.Rat.Lemmas

namespace FourCorner.UniformTorsion

lemma odd_sq_mod_four {z : ℤ} (hz : Odd z) : z^2 % 4 = 1 := by
  have hh := dyadic_odd_square_mod_sixteen hz
  omega

lemma B_mod_four {mu nu : ℤ} (hm : Odd mu) : B mu nu % 4 = 3 := by
  simp [B, Int.sub_emod, odd_sq_mod_four hm]

lemma B_ne_zero {mu nu : ℤ} (hm : Odd mu) : B mu nu ≠ 0 := by
  intro h
  have hh := B_mod_four (nu := nu) hm
  rw [h] at hh
  norm_num at hh

lemma mu_ne_zero_of_odd {mu : ℤ} (hm : Odd mu) : mu ≠ 0 := by
  intro h
  have hh := odd_sq_mod_four hm
  rw [h] at hh
  norm_num at hh

lemma norm_parameter_mod_four {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu) :
    (mu^2-2*nu^2) % 4 = 3 := by
  simp [Int.sub_emod, Int.mul_emod, odd_sq_mod_four hm,
    odd_sq_mod_four hn]

lemma norm_parameter_ne_zero {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu) :
    mu^2-2*nu^2 ≠ 0 := by
  intro h
  have hh := norm_parameter_mod_four hm hn
  rw [h] at hh
  norm_num at hh

lemma twice_norm_parameter_not_rat_square {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu) :
    ¬ ∃ q : ℚ, q^2 = ((2*(mu^2-2*nu^2) : ℤ) : ℚ) := by
  rintro ⟨q, hq⟩
  have hs : IsSquare (((2*(mu^2-2*nu^2) : ℤ) : ℚ)) := ⟨q, by nlinarith⟩
  obtain ⟨z, hz⟩ := Rat.isSquare_intCast_iff.mp hs
  apply Int.sq_ne_two_mod_four z
  rw [← hz, Int.mul_emod, norm_parameter_mod_four hm hn]
  norm_num

lemma alpha_disc_factor (mu nu : ℤ) :
    alpha mu nu ^ 2 - 4 * B mu nu ^ 2 = 32 * mu ^ 2 * (mu ^ 2 - 2 * nu ^ 2) := by
  unfold alpha B
  ring

lemma quadratic_tail_ne_zero {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu) (x : ℚ) :
    x^2 + (alpha mu nu : ℚ)*x + (B mu nu : ℚ)^2 ≠ 0 := by
  intro hx
  have hm0 : (mu : ℚ) ≠ 0 := by exact_mod_cast mu_ne_zero_of_odd hm
  apply twice_norm_parameter_not_rat_square hm hn
  refine ⟨(2*x+(alpha mu nu : ℚ))/(4*(mu : ℚ)), ?_⟩
  have hd : (alpha mu nu : ℚ)^2 - 4*(B mu nu : ℚ)^2 =
      32*(mu : ℚ)^2*((mu : ℚ)^2-2*(nu : ℚ)^2) := by
    exact_mod_cast alpha_disc_factor mu nu
  push_cast
  field_simp
  linear_combination 4*hx + hd

lemma curve_discriminant (mu nu : ℤ) :
    (curve mu nu).Δ = 512*(B mu nu : ℚ)^4*(mu : ℚ)^2*
      ((mu : ℚ)^2-2*(nu : ℚ)^2) := by
  have hd : (alpha mu nu : ℚ)^2 - 4*(B mu nu : ℚ)^2 =
      32*(mu : ℚ)^2*((mu : ℚ)^2-2*(nu : ℚ)^2) := by
    exact_mod_cast alpha_disc_factor mu nu
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination 16*(B mu nu : ℚ)^4*hd

lemma curve_isElliptic {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu) :
    (curve mu nu).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, curve_discriminant]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (pow_ne_zero 4 (by exact_mod_cast B_ne_zero (nu := nu) hm))
    · exact pow_ne_zero 2 (by exact_mod_cast mu_ne_zero_of_odd hm)
  · exact_mod_cast norm_parameter_ne_zero hm hn

/-- The only actual rational points killed by two are infinity and (0,0). -/
theorem two_torsion_cases {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu)
    (P : (curve mu nu).toAffine.Point) (h2 : 2 • P = 0) :
    P = 0 ∨ P = zeroPoint mu nu (B_ne_zero hm) := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y hxy =>
    right
    have hneg : WeierstrassCurve.Affine.Point.some x y hxy =
        -WeierstrassCurve.Affine.Point.some x y hxy := by
      apply add_eq_zero_iff_eq_neg.mp
      simpa only [two_nsmul] using h2
    rw [WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq] at hneg
    have hy : y = 0 := by
      have hh := hneg.2
      simp only [curve, WeierstrassCurve.Affine.negY, zero_mul, sub_zero] at hh
      linarith
    have he := (curve_equation_iff mu nu x y).mp hxy.1
    rw [hy] at he
    have hprod : x*(x^2+(alpha mu nu : ℚ)*x+(B mu nu : ℚ)^2)=0 := by
      linear_combination -he
    have hx : x = 0 := (mul_eq_zero.mp hprod).resolve_right (quadratic_tail_ne_zero hm hn x)
    unfold zeroPoint
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx,hy⟩


lemma B_not_rat_square {mu nu : ℤ} (hm : Odd mu) :
    ¬ ∃ q : ℚ, (B mu nu : ℚ) = q^2 := by
  rintro ⟨q, hq⟩
  have hs : IsSquare (B mu nu : ℚ) := ⟨q, by nlinarith⟩
  obtain ⟨z, hz⟩ := Rat.isSquare_intCast_iff.mp hs
  have hb := B_mod_four (nu := nu) hm
  rw [hz] at hb
  have hh := dyadic_square_mod_sixteen z
  rw [← pow_two] at hb
  omega

#print axioms B_not_rat_square
#print axioms twice_norm_parameter_not_rat_square
#print axioms quadratic_tail_ne_zero
#print axioms curve_isElliptic
#print axioms two_torsion_cases
end FourCorner.UniformTorsion
