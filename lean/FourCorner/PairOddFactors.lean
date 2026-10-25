import FourCorner.RadiusContent
import FourCorner.IntegralModel
import FourCorner.IntegralNormalization
import FourCorner.FermatSymmetry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace FourCorner
namespace IntegralModel

/-- At every prime in the radius content, all four geometric factors in the six
squared radius differences are units. The diagonal factors follow from the
origin square and the nonvanishing of the primitive coordinates. -/
theorem radiusContent_prime_linear_factors (m : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hpg : p ∣ m.radiusContent) :
    ¬ (p : ℤ) ∣ m.L - 2 * m.X ∧
    ¬ (p : ℤ) ∣ m.L - 2 * m.Y ∧
    ¬ (p : ℤ) ∣ m.X - m.Y ∧
    ¬ (p : ℤ) ∣ m.X + m.Y - m.L := by
  have hodd : p ≠ 2 := by intro he; subst p; exact m.radiusContent_odd hpg
  have pg : (p : ℤ) ∣ (m.radiusContent : ℤ) := Int.natCast_dvd_natCast.mpr hpg
  have h₀ := dvd_trans pg m.radiusContent_dvd₀
  have h₁ := dvd_trans pg m.radiusContent_dvd₁
  have h₂ := dvd_trans pg m.radiusContent_dvd₂
  have h₃ := dvd_trans pg m.radiusContent_dvd₃
  obtain ⟨hl, hx, hy, _⟩ := m.common_radius_prime_support hp hodd h₀ h₁ h₂ h₃
  let : Fact p.Prime := ⟨hp⟩
  have l0 : (m.L : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd m.L p).mpr hl
  have x0 : (m.X : ZMod p) ≠ 0 := by
    intro h; exact hx ((ZMod.intCast_zmod_eq_zero_iff_dvd m.X p).mp h)
  have y0 : (m.Y : ZMod p) ≠ 0 := by
    intro h; exact hy ((ZMod.intCast_zmod_eq_zero_iff_dvd m.Y p).mp h)
  have a0 : (m.A₀ : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd m.A₀ p).mpr h₀
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp (by simpa using h)
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (Int.natCast_dvd_natCast.mp hd))
  have e0 : (m.X : ZMod p)^2 + (m.Y : ZMod p)^2 = 0 := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) m.sq₀
    push_cast at h
    simpa [a0] using h.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hd
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (m.L - 2 * m.X) p).mpr hd
    push_cast at h
    rw [l0, zero_sub, neg_eq_zero] at h
    exact (mul_ne_zero htwo x0) h
  · intro hd
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (m.L - 2 * m.Y) p).mpr hd
    push_cast at h
    rw [l0, zero_sub, neg_eq_zero] at h
    exact (mul_ne_zero htwo y0) h
  · intro hd
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (m.X - m.Y) p).mpr hd
    push_cast at h
    have hh : (2 : ZMod p) * (m.X : ZMod p)^2 = 0 := by
      linear_combination e0 + ((m.X : ZMod p) + (m.Y : ZMod p)) * h
    exact (mul_ne_zero htwo (pow_ne_zero 2 x0)) hh
  · intro hd
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (m.X + m.Y - m.L) p).mpr hd
    push_cast at h
    rw [l0, sub_zero] at h
    have hh : (2 : ZMod p) * (m.X : ZMod p)^2 = 0 := by
      linear_combination e0 + ((m.X : ZMod p) - (m.Y : ZMod p)) * h
    exact (mul_ne_zero htwo (pow_ne_zero 2 x0)) hh

/-- The six actual integer radii pairs are distinct, by the strict-point
symmetry exclusions. -/
theorem six_integer_radius_inequalities (m : IntegralModel) :
    m.A₀ ≠ m.A₁ ∧ m.A₀ ≠ m.A₂ ∧ m.A₀ ≠ m.A₃ ∧
    m.A₁ ≠ m.A₂ ∧ m.A₁ ≠ m.A₃ ∧ m.A₂ ≠ m.A₃ := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ :=
    strict_point_six_radius_inequalities m.toStrictPoint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he; exact h01 (by rw [he])
  · intro he; exact h02 (by rw [he])
  · intro he; exact h03 (by rw [he])
  · intro he; exact h12 (by rw [he])
  · intro he; exact h13 (by rw [he])
  · intro he; exact h23 (by rw [he])

/-- The four radii in corner order. -/
def pairRadius (m : IntegralModel) : Fin 4 → ℤ :=
  ![m.A₀, m.A₁, m.A₂, m.A₃]

theorem pairRadius_pos (m : IntegralModel) (i : Fin 4) : 0 < m.pairRadius i := by
  fin_cases i <;> simpa [pairRadius] using
    (by first | exact m.A₀_pos | exact m.A₁_pos | exact m.A₂_pos | exact m.A₃_pos)

theorem pairRadius_odd (m : IntegralModel) (i : Fin 4) : m.pairRadius i % 2 = 1 := by
  obtain ⟨_, _, h₀, h₁, h₂, h₃⟩ := m.four_divides_L_and_orientation
  fin_cases i <;> simp_all [pairRadius]

/-- The actual radius content divides every indexed radius. -/
theorem radiusContent_dvd_pairRadius (m : IntegralModel) (i : Fin 4) :
    (m.radiusContent : ℤ) ∣ m.pairRadius i := by
  fin_cases i <;> simpa [pairRadius] using
    (by first | exact m.radiusContent_dvd₀ | exact m.radiusContent_dvd₁ |
      exact m.radiusContent_dvd₂ | exact m.radiusContent_dvd₃)

/-- The indexed family has exactly the declared common content. -/
theorem dvd_radiusContent_iff (m : IntegralModel) (k : ℕ) :
    k ∣ m.radiusContent ↔ ∀ i : Fin 4, (k : ℤ) ∣ m.pairRadius i := by
  constructor
  · intro hk i
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hk) (m.radiusContent_dvd_pairRadius i)
  · intro hk
    have h₀ : (k : ℤ) ∣ m.A₀ := by simpa [pairRadius] using hk 0
    have h₁ : (k : ℤ) ∣ m.A₁ := by simpa [pairRadius] using hk 1
    have h₂ : (k : ℤ) ∣ m.A₂ := by simpa [pairRadius] using hk 2
    have h₃ : (k : ℤ) ∣ m.A₃ := by simpa [pairRadius] using hk 3
    exact Nat.dvd_gcd (Nat.dvd_gcd (Int.natCast_dvd.mp h₀) (Int.natCast_dvd.mp h₁))
      (Nat.dvd_gcd (Int.natCast_dvd.mp h₂) (Int.natCast_dvd.mp h₃))

/-- The signed linear factor in the difference of two squared radii. -/
def pairDifferenceFactor (m : IntegralModel) : Fin 4 → Fin 4 → ℤ :=
  ![![0, m.L - 2 * m.X, m.L - 2 * m.Y, -2 * (m.X + m.Y - m.L)],
    ![-(m.L - 2 * m.X), 0, 2 * (m.X - m.Y), m.L - 2 * m.Y],
    ![-(m.L - 2 * m.Y), -(2 * (m.X - m.Y)), 0, m.L - 2 * m.X],
    ![-(-2 * (m.X + m.Y - m.L)), -(m.L - 2 * m.Y), -(m.L - 2 * m.X), 0]]

theorem pairRadius_sq_sub (m : IntegralModel) (i j : Fin 4) :
    (m.pairRadius j) ^ 2 - (m.pairRadius i) ^ 2 =
      m.L * m.pairDifferenceFactor i j := by
  fin_cases i <;> fin_cases j <;>
    simp [pairRadius, pairDifferenceFactor, m.sq₀, m.sq₁, m.sq₂, m.sq₃] <;> ring

theorem two_dvd_pairDifferenceFactor (m : IntegralModel) (i j : Fin 4) :
    (2 : ℤ) ∣ m.pairDifferenceFactor i j := by
  have hL := m.basic_mod_four.1
  apply Int.dvd_of_emod_eq_zero
  fin_cases i <;> fin_cases j <;> norm_num [pairDifferenceFactor] <;> omega

theorem two_mul_L_dvd_pairRadius_sq_sub (m : IntegralModel) (i j : Fin 4) :
    2 * m.L ∣ (m.pairRadius j) ^ 2 - (m.pairRadius i) ^ 2 := by
  rw [m.pairRadius_sq_sub]
  obtain ⟨k, hk⟩ := m.two_dvd_pairDifferenceFactor i j
  refine ⟨k, ?_⟩
  rw [hk]
  ring

/-- Distinct labels correspond to distinct actual integer radii. -/
theorem pairRadius_ne (m : IntegralModel) {i j : Fin 4} (hij : i ≠ j) :
    m.pairRadius i ≠ m.pairRadius j := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := m.six_integer_radius_inequalities
  fin_cases i <;> fin_cases j <;> simp_all [pairRadius, ne_comm]

/-- Thus no squared difference for a distinct pair vanishes. -/
theorem pairRadius_sq_sub_ne_zero (m : IntegralModel) {i j : Fin 4} (hij : i ≠ j) :
    (m.pairRadius j)^2 - (m.pairRadius i)^2 ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  exact m.pairRadius_ne hij ((sq_eq_sq₀ (le_of_lt (m.pairRadius_pos j))
    (le_of_lt (m.pairRadius_pos i))).mp h).symm

/-- Every factor in a distinct pair's squared difference is a unit at every
prime dividing the actual radius content. -/
theorem radiusContent_prime_not_dvd_pairDifferenceFactor (m : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hpg : p ∣ m.radiusContent) {i j : Fin 4} (hij : i ≠ j) :
    ¬ (p : ℤ) ∣ m.pairDifferenceFactor i j := by
  obtain ⟨hx, hy, hd, ha⟩ := m.radiusContent_prime_linear_factors hp hpg
  have hodd : p ≠ 2 := by intro he; subst p; exact m.radiusContent_odd hpg
  have hmul {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) : ¬ (p : ℤ) ∣ 2 * z := by
    intro hpz
    have hn : p ∣ 2 * z.natAbs := by
      simpa [Int.natAbs_mul] using (Int.natCast_dvd.mp hpz)
    rcases hp.dvd_mul.mp hn with h2 | hz'
    · exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact hz (Int.natCast_dvd.mpr hz')
  have hxr : ¬ (p : ℤ) ∣ 2 * m.X - m.L := by simpa only [dvd_sub_comm] using hx
  have hyr : ¬ (p : ℤ) ∣ 2 * m.Y - m.L := by simpa only [dvd_sub_comm] using hy
  have h2d := hmul hd
  have h2a := hmul ha
  fin_cases i <;> fin_cases j <;> simp_all [pairDifferenceFactor, neg_mul]

/-- The same unit assertion written in the prime residue field. -/
theorem radiusContent_prime_pairDifferenceFactor_ne_zero (m : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hpg : p ∣ m.radiusContent) {i j : Fin 4} (hij : i ≠ j) :
    (m.pairDifferenceFactor i j : ZMod p) ≠ 0 := by
  intro h
  exact m.radiusContent_prime_not_dvd_pairDifferenceFactor hp hpg hij
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.radiusContent_prime_linear_factors

#print axioms FourCorner.IntegralModel.pairRadius_ne
#print axioms FourCorner.IntegralModel.pairRadius_sq_sub_ne_zero
#print axioms FourCorner.IntegralModel.radiusContent_prime_not_dvd_pairDifferenceFactor
#print axioms FourCorner.IntegralModel.two_mul_L_dvd_pairRadius_sq_sub
