import FourCorner.CommonRootPadicVal
import FourCorner.CriticalSeventeenPadic
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace FourCorner

/-- Removing the actual nonzero square factors from the two ramified source
classes leaves the selected and complementary integer products. -/
theorem commonRoot_remove_square_factors {K : Type*} [Field K]
    {ell d m c u v : K} (hu : u ≠ 0) (hv : v ≠ 0)
    (hm : m ≠ 0) (h2 : (2 : K) ≠ 0)
    (hell : ell = 2 * m * u ^ 2) (hd : d = m * c * v ^ 2)
    (hs : IsSquare ell ∨ IsSquare (d / ell)) :
    IsSquare (2 * m) ∨ IsSquare (2 * c) := by
  rcases hs with hs | hs
  · left
    have h := hs.div (IsSquare.sq u)
    rw [hell, mul_div_cancel_right₀ _ (pow_ne_zero 2 hu)] at h
    exact h
  · right
    have h := hs.mul (IsSquare.sq (2 * u / v))
    have he : d / ell * (2 * u / v) ^ 2 = 2 * c := by
      rw [hd, hell]
      field_simp

    simpa only [he] using h

/-- A prime dividing a squarefree integer has precisely depth one. -/
theorem squarefree_padicValNat_eq_one {p n : ℕ} [Fact p.Prime]
    (hn : Squarefree n) (hpn : p ∣ n) : padicValNat p n = 1 := by
  have hp : p.Prime := Fact.out
  have hlo : 0 < n.factorization p :=
    (Nat.Prime.factorization_pos_of_dvd hp hn.ne_zero hpn)
  have hhi := hn.natFactorization_le_one p
  rw [← Nat.factorization_def n hp]
  omega

/-- At an odd prime, local squarehood of twice a squarefree natural forces
both a unit and a positive Legendre symbol of its unit factor. -/
theorem squarefree_padic_twice_square_unit_character {p n : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hn : Squarefree n) (h2 : legendreSym p 2 = 1)
    (hs : IsSquare ((2 * n : ℕ) : ℚ_[p])) :
    ¬ p ∣ n ∧ legendreSym p (n : ℤ) = 1 := by
  have hnz : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn.ne_zero
  have h2z : (2 : ℚ_[p]) ≠ 0 := by norm_num
  have hunit : ¬ p ∣ n := by
    intro hd
    have hv := commonRoot_even_val_of_isSquare hs
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hv
    rw [Padic.valuation_mul h2z hnz,
      commonRoot_val_two hp, zero_add, Padic.valuation_natCast,
      squarefree_padicValNat_eq_one hn hd] at hv
    norm_num at hv
  have hnZ : (n : ZMod p) ≠ 0 := by
    intro hz
    exact hunit ((ZMod.natCast_eq_zero_iff n p).mp hz)
  have htwoZ : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hprodZ : ((2 * (n : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using mul_ne_zero htwoZ hnZ
  have hsZ : IsSquare ((2 * (n : ℤ) : ℤ) : ZMod p) :=
    isSquare_zmod_of_isSquare_padic _ (by exact_mod_cast hs)
  have hleg := (legendreSym.eq_one_iff p hprodZ).mpr hsZ
  rw [legendreSym.mul, h2, one_mul] at hleg
  exact ⟨hunit, hleg⟩

end FourCorner

#print axioms FourCorner.commonRoot_remove_square_factors
#print axioms FourCorner.squarefree_padic_twice_square_unit_character
