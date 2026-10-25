import FourCorner.IntegralModel
import FourCorner.PrimitivePrimeSupport
import FourCorner.SupportProductEight
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace FourCorner

lemma integer_square_mod_four (z : ℤ) : z ^ 2 % 4 = 0 ∨ z ^ 2 % 4 = 1 := by
  have h0 := Int.emod_nonneg z (by norm_num : (4:ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos z (by norm_num : (0:ℤ) < 4)
  interval_cases h : z % 4 <;> norm_num [pow_two,Int.mul_emod, h]

lemma integer_square_mod_three (z : ℤ) : z ^ 2 % 3 = 0 ∨ z ^ 2 % 3 = 1 := by
  have h0 := Int.emod_nonneg z (by norm_num : (3:ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos z (by norm_num : (0:ℤ) < 3)
  interval_cases h : z % 3 <;> norm_num [pow_two,Int.mul_emod, h]

lemma IntegralModel.common_divisor_eq_one (M : IntegralModel) {p : ℕ}
    (hX : (p:ℤ) ∣ M.X) (hY : (p:ℤ) ∣ M.Y) (hL : (p:ℤ) ∣ M.L) : p = 1 := by
  have h : p ∣ Nat.gcd (Nat.gcd M.X.natAbs M.Y.natAbs) M.L.natAbs :=
    Nat.dvd_gcd (Nat.dvd_gcd (Int.natCast_dvd.mp hX) (Int.natCast_dvd.mp hY))
      (Int.natCast_dvd.mp hL)
  rw [M.primitive] at h
  exact Nat.dvd_one.mp h

lemma IntegralModel.basic_mod_four (M : IntegralModel) :
    M.L % 2 = 0 ∧ (M.X % 2 = 1 ∧ M.Y % 2 = 0 ∨ M.X % 2 = 0 ∧ M.Y % 2 = 1) := by
  have s0 := integer_square_mod_four M.A₀
  have s1 := integer_square_mod_four M.A₁
  have s2 := integer_square_mod_four M.A₂
  have s3 := integer_square_mod_four M.A₃
  rw [M.sq₀] at s0
  rw [M.sq₁] at s1
  rw [M.sq₂] at s2
  rw [M.sq₃] at s3
  have s := And.intro s0 (And.intro s1 (And.intro s2 s3))
  have primitive2 : ¬ (M.L % 2 = 0 ∧ M.X % 2 = 0 ∧ M.Y % 2 = 0) := by
    rintro ⟨hL,hX,hY⟩
    have := M.common_divisor_eq_one (p:=2) (Int.dvd_of_emod_eq_zero hX)
      (Int.dvd_of_emod_eq_zero hY) (Int.dvd_of_emod_eq_zero hL)
    norm_num at this
  have l0 := Int.emod_nonneg M.L (by norm_num : (4:ℤ) ≠ 0)
  have l1 := Int.emod_lt_of_pos M.L (by norm_num : (0:ℤ) < 4)
  have x0 := Int.emod_nonneg M.X (by norm_num : (4:ℤ) ≠ 0)
  have x1 := Int.emod_lt_of_pos M.X (by norm_num : (0:ℤ) < 4)
  have y0 := Int.emod_nonneg M.Y (by norm_num : (4:ℤ) ≠ 0)
  have y1 := Int.emod_lt_of_pos M.Y (by norm_num : (0:ℤ) < 4)
  interval_cases hl : M.L % 4 <;> interval_cases hx : M.X % 4 <;>
    interval_cases hy : M.Y % 4 <;>
    norm_num [Int.add_emod,Int.sub_emod,pow_two,Int.mul_emod,hl,hx,hy] at s <;> omega

lemma integer_odd_square_mod_eight (z : ℤ) (hz : z % 2 = 1) : z ^ 2 % 8 = 1 := by
  have h0 := Int.emod_nonneg z (by norm_num : (8:ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos z (by norm_num : (0:ℤ) < 8)
  interval_cases h : z % 8 <;> norm_num [pow_two,Int.mul_emod,h] <;> omega

lemma triangle_odd_leg_mod_eight (a b c : ℤ) (ha : a % 2 = 1)
    (hs : c ^ 2 = a ^ 2 + b ^ 2) : b % 4 = 0 ∧ c % 2 = 1 := by
  have ha8 := integer_odd_square_mod_eight a ha
  have hs8 := congrArg (fun z : ℤ => z % 8) hs
  rw [Int.add_emod, ha8] at hs8
  have b0 := Int.emod_nonneg b (by norm_num : (8:ℤ) ≠ 0)
  have b1 := Int.emod_lt_of_pos b (by norm_num : (0:ℤ) < 8)
  have c0 := Int.emod_nonneg c (by norm_num : (8:ℤ) ≠ 0)
  have c1 := Int.emod_lt_of_pos c (by norm_num : (0:ℤ) < 8)
  interval_cases hb : b % 8 <;> interval_cases hc : c % 8 <;>
    norm_num [pow_two,Int.mul_emod,hb,hc] at hs8 <;> omega

lemma IntegralModel.four_divides_L_and_orientation (M : IntegralModel) :
    M.L % 4 = 0 ∧
    (M.X % 2 = 1 ∧ M.Y % 4 = 0 ∨ M.Y % 2 = 1 ∧ M.X % 4 = 0) ∧
    M.A₀ % 2 = 1 ∧ M.A₁ % 2 = 1 ∧ M.A₂ % 2 = 1 ∧ M.A₃ % 2 = 1 := by
  obtain ⟨hl, hor⟩ := M.basic_mod_four
  rcases hor with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · have hlx : (M.L-M.X)%2 = 1 := by omega
    obtain ⟨hy4,ha0⟩ := triangle_odd_leg_mod_eight M.X M.Y M.A₀ hx M.sq₀
    obtain ⟨_,ha1⟩ := triangle_odd_leg_mod_eight (M.L-M.X) M.Y M.A₁ hlx M.sq₁
    obtain ⟨hly4,ha2⟩ := triangle_odd_leg_mod_eight M.X (M.L-M.Y) M.A₂ hx M.sq₂
    obtain ⟨_,ha3⟩ := triangle_odd_leg_mod_eight (M.L-M.X) (M.L-M.Y) M.A₃ hlx M.sq₃
    exact ⟨by omega, Or.inl ⟨hx,hy4⟩,ha0,ha1,ha2,ha3⟩
  · have hly : (M.L-M.Y)%2 = 1 := by omega
    obtain ⟨hx4,ha0⟩ := triangle_odd_leg_mod_eight M.Y M.X M.A₀ hy (by rw [M.sq₀]; ring)
    obtain ⟨hlx4,ha1⟩ := triangle_odd_leg_mod_eight M.Y (M.L-M.X) M.A₁ hy (by rw [M.sq₁]; ring)
    obtain ⟨_,ha2⟩ := triangle_odd_leg_mod_eight (M.L-M.Y) M.X M.A₂ hly (by rw [M.sq₂]; ring)
    obtain ⟨_,ha3⟩ := triangle_odd_leg_mod_eight (M.L-M.Y) (M.L-M.X) M.A₃ hly (by rw [M.sq₃]; ring)
    exact ⟨by omega, Or.inr ⟨hy,hx4⟩,ha0,ha1,ha2,ha3⟩

lemma IntegralModel.three_divides_L (M : IntegralModel) : M.L % 3 = 0 := by
  have s0 := integer_square_mod_three M.A₀
  have s1 := integer_square_mod_three M.A₁
  have s2 := integer_square_mod_three M.A₂
  have s3 := integer_square_mod_three M.A₃
  rw [M.sq₀] at s0
  rw [M.sq₁] at s1
  rw [M.sq₂] at s2
  rw [M.sq₃] at s3
  have s := And.intro s0 (And.intro s1 (And.intro s2 s3))
  have l0 := Int.emod_nonneg M.L (by norm_num : (3:ℤ) ≠ 0)
  have l1 := Int.emod_lt_of_pos M.L (by norm_num : (0:ℤ) < 3)
  have x0 := Int.emod_nonneg M.X (by norm_num : (3:ℤ) ≠ 0)
  have x1 := Int.emod_lt_of_pos M.X (by norm_num : (0:ℤ) < 3)
  have y0 := Int.emod_nonneg M.Y (by norm_num : (3:ℤ) ≠ 0)
  have y1 := Int.emod_lt_of_pos M.Y (by norm_num : (0:ℤ) < 3)
  interval_cases hl : M.L % 3 <;> interval_cases hx : M.X % 3 <;>
    interval_cases hy : M.Y % 3 <;>
    norm_num [Int.add_emod,Int.sub_emod,pow_two,Int.mul_emod,hl,hx,hy] at s <;> omega

lemma IntegralModel.coordinate_three_pattern (M : IntegralModel) :
    (M.X % 3 = 0 ∧ M.Y % 3 ≠ 0) ∨ (M.Y % 3 = 0 ∧ M.X % 3 ≠ 0) := by
  have hl := M.three_divides_L
  have s0 := integer_square_mod_three M.A₀
  rw [M.sq₀] at s0
  have hprimitive : ¬(M.X%3=0 ∧ M.Y%3=0) := by
    rintro ⟨hx,hy⟩
    have := M.common_divisor_eq_one (p:=3) (Int.dvd_of_emod_eq_zero hx)
      (Int.dvd_of_emod_eq_zero hy) (Int.dvd_of_emod_eq_zero hl)
    norm_num at this
  have x0 := Int.emod_nonneg M.X (by norm_num : (3:ℤ) ≠ 0)
  have x1 := Int.emod_lt_of_pos M.X (by norm_num : (0:ℤ) < 3)
  have y0 := Int.emod_nonneg M.Y (by norm_num : (3:ℤ) ≠ 0)
  have y1 := Int.emod_lt_of_pos M.Y (by norm_num : (0:ℤ) < 3)
  interval_cases hx : M.X % 3 <;> interval_cases hy : M.Y % 3 <;>
    norm_num [Int.add_emod,pow_two,Int.mul_emod,hx,hy] at s0 <;> omega

lemma IntegralModel.radii_three_units (M : IntegralModel) :
    M.A₀%3 ≠ 0 ∧ M.A₁%3 ≠ 0 ∧ M.A₂%3 ≠ 0 ∧ M.A₃%3 ≠ 0 := by
  have hl := M.three_divides_L
  have hxy := M.coordinate_three_pattern
  have s0 := congrArg (fun z : ℤ => z % 3) M.sq₀
  have s1 := congrArg (fun z : ℤ => z % 3) M.sq₁
  have s2 := congrArg (fun z : ℤ => z % 3) M.sq₂
  have s3 := congrArg (fun z : ℤ => z % 3) M.sq₃
  have s := And.intro s0 (And.intro s1 (And.intro s2 s3))
  have x0 := Int.emod_nonneg M.X (by norm_num : (3:ℤ) ≠ 0)
  have x1 := Int.emod_lt_of_pos M.X (by norm_num : (0:ℤ) < 3)
  have y0 := Int.emod_nonneg M.Y (by norm_num : (3:ℤ) ≠ 0)
  have y1 := Int.emod_lt_of_pos M.Y (by norm_num : (0:ℤ) < 3)
  interval_cases hx : M.X % 3 <;> interval_cases hy : M.Y % 3 <;>
    norm_num [hx,hy] at hxy <;>
    norm_num [Int.add_emod,Int.sub_emod,pow_two,Int.mul_emod,hl,hx,hy] at s <;>
    refine ⟨?_,?_,?_,?_⟩ <;> intro h <;> norm_num [h] at s

/-- The diagonal product has no zero factor; already forced by parity. -/
lemma IntegralModel.diagonal_product_ne_zero (M : IntegralModel) :
    (M.X-M.Y)*(M.X+M.Y-M.L) ≠ 0 := by
  obtain ⟨hl,hor⟩ := M.basic_mod_four
  apply mul_ne_zero <;> intro h <;> omega

/-- Every prime factor of the actual diagonal product splits 2. -/
theorem IntegralModel.diagonal_prime_support (M : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hd : (p:ℤ) ∣ (M.X-M.Y)*(M.X+M.Y-M.L)) :
    p%8=1 ∨ p%8=7 := by
  obtain ⟨hl,hor⟩ := M.basic_mod_four
  apply M.prime_dvd_diagonal_product (Int.dvd_of_emod_eq_zero hl) (by omega) hp hd

lemma IntegralModel.eight_divides_L (M : IntegralModel) : M.L % 8 = 0 := by
  obtain ⟨hl4,hor,_⟩ := M.four_divides_L_and_orientation
  have hp := int_mod_eight_of_prime_divisors ((M.X-M.Y)*(M.X+M.Y-M.L))
    M.diagonal_product_ne_zero (fun _ hp hd => M.diagonal_prime_support hp hd)
  by_contra hn
  have hl8 : M.L%8=4 := by omega
  have x0 := Int.emod_nonneg M.X (by norm_num : (8:ℤ) ≠ 0)
  have x1 := Int.emod_lt_of_pos M.X (by norm_num : (0:ℤ) < 8)
  have y0 := Int.emod_nonneg M.Y (by norm_num : (8:ℤ) ≠ 0)
  have y1 := Int.emod_lt_of_pos M.Y (by norm_num : (0:ℤ) < 8)
  interval_cases hx : M.X%8 <;> interval_cases hy : M.Y%8 <;>
    norm_num [Int.mul_emod,Int.sub_emod,Int.add_emod,hl8,hx,hy] at hp <;> omega

/-- Divisibility of the actual primitive coordinate denominator by 24. -/
theorem IntegralModel.twentyfour_dvd_L (M : IntegralModel) : (24:ℤ) ∣ M.L := by
  have h8 := M.eight_divides_L
  have h3 := M.three_divides_L
  apply Int.dvd_of_emod_eq_zero
  omega

/-- Manuscript Proposition int:primitive, for its actual primitive integer model. -/
theorem IntegralModel.primitive_congruences (M : IntegralModel) :
    (24:ℤ) ∣ M.L ∧
    (M.X%2=1 ∧ (4:ℤ)∣M.Y ∨ M.Y%2=1 ∧ (4:ℤ)∣M.X) ∧
    (M.A₀%2=1 ∧ M.A₁%2=1 ∧ M.A₂%2=1 ∧ M.A₃%2=1) ∧
    (M.A₀%3≠0 ∧ M.A₁%3≠0 ∧ M.A₂%3≠0 ∧ M.A₃%3≠0) ∧
    (∀ p:ℕ, p.Prime → (p:ℤ)∣(M.X-M.Y)*(M.X+M.Y-M.L) → p%8=1 ∨ p%8=7) := by
  obtain ⟨_,hor,ho⟩ := M.four_divides_L_and_orientation
  refine ⟨M.twentyfour_dvd_L, ?_, ho, M.radii_three_units, ?_⟩
  · rcases hor with ⟨hx,hy⟩ | ⟨hy,hx⟩
    · exact Or.inl ⟨hx,Int.dvd_of_emod_eq_zero hy⟩
    · exact Or.inr ⟨hy,Int.dvd_of_emod_eq_zero hx⟩
  · intro p hp hd
    exact M.diagonal_prime_support hp hd

end FourCorner
#print axioms FourCorner.IntegralModel.basic_mod_four
#print axioms FourCorner.IntegralModel.four_divides_L_and_orientation
#print axioms FourCorner.IntegralModel.radii_three_units
#print axioms FourCorner.IntegralModel.twentyfour_dvd_L
#print axioms FourCorner.IntegralModel.primitive_congruences
