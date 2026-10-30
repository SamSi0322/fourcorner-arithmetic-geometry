import EllipticCurves.ReductionAtPrime
import Mathlib.Data.ZMod.QuotientRing
import FourCorner.CommonRootPadicResidue
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace FourCorner.CommonSource
open IsDedekindDomain

/-- The actual prime ideal `(q)` of the integers. -/
def primeIdeal (q : ℕ) [Fact q.Prime] : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(q : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : q.Prime).ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp Fact.out)
  ne_bot := by simp [(Fact.out : q.Prime).ne_zero]

/-- The canonical identification of the integral residue field with `ZMod q`. -/
noncomputable abbrev residueEquiv (q : ℕ) [Fact q.Prime] :
    (ℤ ⧸ (primeIdeal q).asIdeal) ≃+* ZMod q :=
  Int.quotientSpanNatEquivZMod q

theorem valuation_equiv_padic (q : ℕ) [Fact q.Prime] :
    ((primeIdeal q).valuation ℚ).IsEquiv (Rat.padicValuation q) := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  rw [Rat.valuation_le_one_iff_den, Rat.padicValuation_le_one_iff]
  simp [primeIdeal, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

theorem valuation_le_one_iff_norm (q : ℕ) [Fact q.Prime] (x : ℚ) :
    (primeIdeal q).valuation ℚ x ≤ 1 ↔ ‖(x : ℚ_[q])‖ ≤ 1 := by
  rw [(valuation_equiv_padic q).le_one_iff_le_one,
    Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast]
  by_cases hx : x = 0
  · simp [hx]
  · simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hx]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

theorem valuation_lt_one_iff_norm (q : ℕ) [Fact q.Prime] (x : ℚ) :
    (primeIdeal q).valuation ℚ x < 1 ↔ ‖(x : ℚ_[q])‖ < 1 := by
  rw [(valuation_equiv_padic q).lt_one_iff_lt_one]
  by_cases hx : x = 0
  · simp [hx]
  have hx' : (x : ℚ_[q]) ≠ 0 := by exact_mod_cast hx
  rw [Padic.norm_eq_zpow_neg_valuation hx', Padic.valuation_ratCast]
  have hq : 1 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  rw [← zpow_zero (q : ℝ), (zpow_right_strictMono₀ hq).lt_iff_lt]
  simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hx]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]

/-- The same rational number, viewed as an actual integral `q`-adic number. -/
noncomputable def rationalIntegral (q : ℕ) [Fact q.Prime] (x : ℚ)
    (hx : (primeIdeal q).valuation ℚ x ≤ 1) : ℤ_[q] :=
  ⟨(x : ℚ_[q]), (valuation_le_one_iff_norm q x).mp hx⟩

@[simp] theorem rationalIntegral_coe (q : ℕ) [Fact q.Prime] (x : ℚ)
    (hx : (primeIdeal q).valuation ℚ x ≤ 1) :
    (rationalIntegral q x hx : ℚ_[q]) = (x : ℚ_[q]) := rfl

/-- Algebraic prime-ideal reduction and the actual completed-field residue agree. -/
theorem residue_compatibility (q : ℕ) [Fact q.Prime] (x : ℚ)
    (hx : (primeIdeal q).valuation ℚ x ≤ 1) :
    residueEquiv q (HeightOneSpectrum.residueHom (primeIdeal q) ⟨x, hx⟩) =
      PadicInt.toZMod (rationalIntegral q x hx) := by
  obtain ⟨a, ha⟩ := (primeIdeal q).exists_valuation_sub_lt_of_integer hx 1
  have ha' : (primeIdeal q).valuation ℚ ((a : ℚ) - x) < 1 := by
    simpa using ha
  rw [HeightOneSpectrum.residueHom_eq (primeIdeal q) ha']
  have hn : ‖((a : ℤ_[q]) - rationalIntegral q x hx : ℤ_[q])‖ < 1 := by
    change ‖(a : ℚ_[q]) - (x : ℚ_[q])‖ < 1
    simpa only [Rat.cast_sub, Rat.cast_intCast] using
      (valuation_lt_one_iff_norm q ((a : ℚ) - x)).mp ha'
  have hz := (padicInt_norm_lt_one_iff_residue_zero
    ((a : ℤ_[q]) - rationalIntegral q x hx)).mp hn
  have he : (a : ZMod q) = PadicInt.toZMod (rationalIntegral q x hx) := by
    simpa only [map_sub, map_intCast, sub_eq_zero] using hz
  exact he

/-- A vanishing algebraic residue is exactly the open unit ball in `ℚ_q`. -/
theorem residue_eq_zero_iff_norm_lt_one (q : ℕ) [Fact q.Prime] (x : ℚ)
    (hx : (primeIdeal q).valuation ℚ x ≤ 1) :
    residueEquiv q (HeightOneSpectrum.residueHom (primeIdeal q) ⟨x, hx⟩) = 0 ↔
      ‖(x : ℚ_[q])‖ < 1 := by
  rw [residue_compatibility, ← padicInt_norm_lt_one_iff_residue_zero]
  rfl

/-- Every integral residue disk is the corresponding actual `q`-adic open ball. -/
theorem residue_eq_int_iff_norm_sub_lt_one (q : ℕ) [Fact q.Prime] (x : ℚ)
    (hx : (primeIdeal q).valuation ℚ x ≤ 1) (a : ℤ) :
    residueEquiv q (HeightOneSpectrum.residueHom (primeIdeal q) ⟨x, hx⟩) = (a : ZMod q) ↔
      ‖(x : ℚ_[q]) - (a : ℚ_[q])‖ < 1 := by
  rw [residue_compatibility]
  have he := padicInt_norm_lt_one_iff_residue_zero
    (rationalIntegral q x hx - (a : ℤ_[q]))
  simpa only [map_sub, map_intCast, sub_eq_zero, PadicInt.norm_def, PadicInt.coe_sub,
    PadicInt.coe_intCast, rationalIntegral_coe] using he.symm

/-- An integer prime to `q` has unit norm in the actual completed field. -/
theorem int_norm_eq_one_of_not_dvd (q : ℕ) [Fact q.Prime] (a : ℤ)
    (ha : ¬ (q : ℤ) ∣ a) : ‖(a : ℚ_[q])‖ = 1 := by
  apply le_antisymm (Padic.norm_int_le_one a)
  apply le_of_not_gt
  intro h
  exact ha (Padic.norm_intCast_lt_one_iff.mp h)

end FourCorner.CommonSource
