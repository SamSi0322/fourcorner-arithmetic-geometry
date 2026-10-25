import FourCorner.IntegralModel
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Ring

namespace FourCorner

private theorem primitive_not_all_zero_mod (m : IntegralModel) {p : ℕ} (hp : p.Prime)
    (hx : (m.X : ZMod p) = 0) (hy : (m.Y : ZMod p) = 0) :
    (m.L : ZMod p) ≠ 0 := by
  intro hl
  have hd (a : ℤ) (h : (a : ZMod p) = 0) : p ∣ a.natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h))
  have h := Nat.dvd_gcd (Nat.dvd_gcd (hd _ hx) (hd _ hy)) (hd _ hl)
  rw [m.primitive] at h
  exact hp.not_dvd_one h

private theorem two_square_of_eq_double_square {p : ℕ} [Fact p.Prime]
    {a b : ZMod p} (hb : b ≠ 0) (hs : a ^ 2 = 2 * b ^ 2) :
    IsSquare (2 : ZMod p) := by
  refine ⟨a / b, ?_⟩
  rw [← pow_two, div_pow, eq_div_iff (pow_ne_zero 2 hb)]
  exact hs.symm

/-- Every prime factor of the diagonal product is `1` or `7` modulo `8`.
The parity assumptions are supplied by the primitive parity theorem. -/
theorem IntegralModel.prime_dvd_diagonal_product (m : IntegralModel)
    (hL : (2 : ℤ) ∣ m.L) (hXY : m.X % 2 ≠ m.Y % 2)
    {p : ℕ} (hp : p.Prime) (hd : (p : ℤ) ∣ (m.X - m.Y) * (m.X + m.Y - m.L)) :
    p % 8 = 1 ∨ p % 8 = 7 := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    have hl := Int.emod_eq_zero_of_dvd hL
    rcases Int.prime_two.dvd_or_dvd hd with hd | hd
    · have h := Int.emod_eq_zero_of_dvd hd
      omega
    · have h := Int.emod_eq_zero_of_dvd hd
      omega
  let : Fact p.Prime := ⟨hp⟩
  apply (ZMod.exists_sq_eq_two_iff hp2).mp
  have h₀ : (m.A₀ : ZMod p) ^ 2 = (m.X : ZMod p) ^ 2 + (m.Y : ZMod p) ^ 2 := by
    simpa only [Int.cast_pow, Int.cast_add, Int.cast_sub] using
      congrArg (fun a : ℤ => (a : ZMod p)) m.sq₀
  have h₁ : (m.A₁ : ZMod p) ^ 2 = ((m.L : ZMod p) - m.X) ^ 2 + (m.Y : ZMod p) ^ 2 := by
    simpa only [Int.cast_pow, Int.cast_add, Int.cast_sub] using
      congrArg (fun a : ℤ => (a : ZMod p)) m.sq₁
  have h₂ : (m.A₂ : ZMod p) ^ 2 = (m.X : ZMod p) ^ 2 + ((m.L : ZMod p) - m.Y) ^ 2 := by
    simpa only [Int.cast_pow, Int.cast_add, Int.cast_sub] using
      congrArg (fun a : ℤ => (a : ZMod p)) m.sq₂
  have h₃ : (m.A₃ : ZMod p) ^ 2 = ((m.L : ZMod p) - m.X) ^ 2 + ((m.L : ZMod p) - m.Y) ^ 2 := by
    simpa only [Int.cast_pow, Int.cast_add, Int.cast_sub] using
      congrArg (fun a : ℤ => (a : ZMod p)) m.sq₃
  have hprod : ((m.X : ZMod p) - m.Y) * ((m.X : ZMod p) + m.Y - m.L) = 0 := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
  rcases mul_eq_zero.mp hprod with hdiag | hdiag
  · have hxy : (m.X : ZMod p) = m.Y := sub_eq_zero.mp hdiag
    by_cases hx : (m.X : ZMod p) = 0
    · have hy : (m.Y : ZMod p) = 0 := hxy.symm.trans hx
      have hl := primitive_not_all_zero_mod m hp hx hy
      apply two_square_of_eq_double_square hl (a := (m.A₃ : ZMod p))
      simpa [hx, hy, two_mul] using h₃
    · apply two_square_of_eq_double_square hx (a := (m.A₀ : ZMod p))
      simpa [← hxy, two_mul] using h₀
  · have hsum : (m.X : ZMod p) + m.Y = m.L := sub_eq_zero.mp hdiag
    by_cases hy : (m.Y : ZMod p) = 0
    · have hxl : (m.X : ZMod p) = m.L := by simpa [hy] using hsum
      have hx : (m.X : ZMod p) ≠ 0 := by
        intro hx
        exact primitive_not_all_zero_mod m hp hx hy (hxl.symm.trans hx)
      apply two_square_of_eq_double_square hx (a := (m.A₂ : ZMod p))
      simpa [hy, ← hxl, two_mul] using h₂
    · apply two_square_of_eq_double_square hy (a := (m.A₁ : ZMod p))
      have hly : (m.L : ZMod p) - m.X = m.Y := by rw [← hsum]; ring
      simpa [hly, two_mul] using h₁

#print axioms IntegralModel.prime_dvd_diagonal_product

end FourCorner
