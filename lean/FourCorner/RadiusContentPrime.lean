import FourCorner.IntegralModel
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.NatPrime
import Mathlib.Tactic.Push
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace FourCorner
namespace IntegralModel

private theorem two_ne_zero_mod_prime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdi : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp (by simpa using h)
  have hd : p ∣ 2 := Int.natCast_dvd_natCast.mp hdi
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)

/-- An odd prime common to the four radii divides the square side. -/
theorem common_radius_prime_dvd_L (m : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (h₀ : (p : ℤ) ∣ m.A₀) (h₁ : (p : ℤ) ∣ m.A₁)
    (h₂ : (p : ℤ) ∣ m.A₂) (_h₃ : (p : ℤ) ∣ m.A₃) :
    (p : ℤ) ∣ m.L := by
  let : Fact p.Prime := ⟨hp⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd m.L p).mp
  have a₀ : (m.A₀ : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd m.A₀ p).mpr h₀
  have a₁ : (m.A₁ : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd m.A₁ p).mpr h₁
  have a₂ : (m.A₂ : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd m.A₂ p).mpr h₂
  have e₀ : (m.X : ZMod p)^2 + (m.Y : ZMod p)^2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) m.sq₀
    push_cast at this
    simpa [a₀] using this.symm
  have e₁ : ((m.L : ZMod p) - (m.X : ZMod p))^2 + (m.Y : ZMod p)^2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) m.sq₁
    push_cast at this
    simpa [a₁] using this.symm
  have e₂ : (m.X : ZMod p)^2 + ((m.L : ZMod p) - (m.Y : ZMod p))^2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) m.sq₂
    push_cast at this
    simpa [a₂] using this.symm
  by_contra hl
  have hx : (m.L : ZMod p) - 2 * (m.X : ZMod p) = 0 := by
    apply (mul_eq_zero.mp (show (m.L : ZMod p) * ((m.L : ZMod p) - 2 * (m.X : ZMod p)) = 0 from ?_)).resolve_left hl
    linear_combination e₁ - e₀
  have hy : (m.L : ZMod p) - 2 * (m.Y : ZMod p) = 0 := by
    apply (mul_eq_zero.mp (show (m.L : ZMod p) * ((m.L : ZMod p) - 2 * (m.Y : ZMod p)) = 0 from ?_)).resolve_left hl
    linear_combination e₂ - e₀
  have hh : (2 : ZMod p) * (m.L : ZMod p)^2 = 0 := by
    linear_combination 4 * e₀ + ((m.L : ZMod p) + 2 * (m.X : ZMod p)) * hx +
      ((m.L : ZMod p) + 2 * (m.Y : ZMod p)) * hy
  exact hl (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hh).resolve_left (two_ne_zero_mod_prime hp hodd)))

private theorem not_prime_dvd_coordinates (m : IntegralModel) {p : ℕ} (hp : p.Prime)
    (hx : (p : ℤ) ∣ m.X) (hy : (p : ℤ) ∣ m.Y) (hl : (p : ℤ) ∣ m.L) : False := by
  have hg := Nat.dvd_gcd (Nat.dvd_gcd (Int.natCast_dvd.mp hx) (Int.natCast_dvd.mp hy))
    (Int.natCast_dvd.mp hl)
  rw [m.primitive] at hg
  exact hp.not_dvd_one hg

/-- Primitivity prevents a common odd radius prime from dividing the first coordinate. -/
theorem common_radius_prime_not_dvd_X (m : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (h₀ : (p : ℤ) ∣ m.A₀) (h₁ : (p : ℤ) ∣ m.A₁)
    (h₂ : (p : ℤ) ∣ m.A₂) (h₃ : (p : ℤ) ∣ m.A₃) :
    ¬ (p : ℤ) ∣ m.X := by
  intro hx
  have hl := m.common_radius_prime_dvd_L hp hodd h₀ h₁ h₂ h₃
  have hy2 : (p : ℤ) ∣ m.Y ^ 2 := by
    have hd := dvd_sub (dvd_pow h₀ (by decide : 2 ≠ 0)) (dvd_pow hx (by decide : 2 ≠ 0))
    rw [m.sq₀] at hd
    simpa using hd
  have hy : (p : ℤ) ∣ m.Y := Int.natCast_dvd.mpr (Int.Prime.dvd_natAbs_of_coe_dvd_sq hp m.Y hy2)
  exact m.not_prime_dvd_coordinates hp hx hy hl

/-- Primitivity prevents a common odd radius prime from dividing the second coordinate. -/
theorem common_radius_prime_not_dvd_Y (m : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (h₀ : (p : ℤ) ∣ m.A₀) (h₁ : (p : ℤ) ∣ m.A₁)
    (h₂ : (p : ℤ) ∣ m.A₂) (h₃ : (p : ℤ) ∣ m.A₃) :
    ¬ (p : ℤ) ∣ m.Y := by
  intro hy
  have hl := m.common_radius_prime_dvd_L hp hodd h₀ h₁ h₂ h₃
  have hx2 : (p : ℤ) ∣ m.X ^ 2 := by
    have hd := dvd_sub (dvd_pow h₀ (by decide : 2 ≠ 0)) (dvd_pow hy (by decide : 2 ≠ 0))
    rw [m.sq₀] at hd
    simpa using hd
  have hx : (p : ℤ) ∣ m.X := Int.natCast_dvd.mpr (Int.Prime.dvd_natAbs_of_coe_dvd_sq hp m.X hx2)
  exact m.not_prime_dvd_coordinates hp hx hy hl

/-- Every odd prime in the common radius content is congruent to one modulo four. -/
theorem common_radius_prime_mod_four (m : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (h₀ : (p : ℤ) ∣ m.A₀) (h₁ : (p : ℤ) ∣ m.A₁)
    (h₂ : (p : ℤ) ∣ m.A₂) (h₃ : (p : ℤ) ∣ m.A₃) :
    p % 4 = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hy : (m.Y : ZMod p) ≠ 0 := by
    intro hy
    exact m.common_radius_prime_not_dvd_Y hp hodd h₀ h₁ h₂ h₃
      ((ZMod.intCast_zmod_eq_zero_iff_dvd m.Y p).mp hy)
  have ha : (m.A₀ : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd m.A₀ p).mpr h₀
  have hs : (m.X : ZMod p)^2 + (m.Y : ZMod p)^2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) m.sq₀
    push_cast at this
    simpa [ha] using this.symm
  have hn3 : p % 4 ≠ 3 :=
    ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy (eq_neg_of_add_eq_zero_left hs)
  exact (Nat.odd_mod_four_iff.mp (hp.eq_two_or_odd.resolve_left hodd)).resolve_right hn3

/-- The complete prime-support conclusion, still attached to the primitive four-square model. -/
theorem common_radius_prime_support (m : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (h₀ : (p : ℤ) ∣ m.A₀) (h₁ : (p : ℤ) ∣ m.A₁)
    (h₂ : (p : ℤ) ∣ m.A₂) (h₃ : (p : ℤ) ∣ m.A₃) :
    (p : ℤ) ∣ m.L ∧ ¬ (p : ℤ) ∣ m.X ∧ ¬ (p : ℤ) ∣ m.Y ∧ p % 4 = 1 :=
  ⟨m.common_radius_prime_dvd_L hp hodd h₀ h₁ h₂ h₃,
   m.common_radius_prime_not_dvd_X hp hodd h₀ h₁ h₂ h₃,
   m.common_radius_prime_not_dvd_Y hp hodd h₀ h₁ h₂ h₃,
   m.common_radius_prime_mod_four hp hodd h₀ h₁ h₂ h₃⟩

#print axioms common_radius_prime_dvd_L
#print axioms common_radius_prime_not_dvd_X
#print axioms common_radius_prime_not_dvd_Y
#print axioms common_radius_prime_mod_four
#print axioms common_radius_prime_support

end IntegralModel
end FourCorner
