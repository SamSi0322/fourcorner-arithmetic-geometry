import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

set_option autoImplicit false

namespace FourCorner

open Polynomial

private theorem norm_lt_one_iff_residue_zero {p : ℕ} [Fact p.Prime]
    (x : ℤ_[p]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal,
    ← PadicInt.ker_toZMod, RingHom.mem_ker]

private theorem norm_eq_one_of_residue_ne_zero {p : ℕ} [Fact p.Prime]
    (x : ℤ_[p]) (hx : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 := by
  apply le_antisymm (PadicInt.norm_le_one x)
  exact le_of_not_gt (fun h => hx ((norm_lt_one_iff_residue_zero x).mp h))

private theorem two_residue_ne_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  exact Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)

/-- A square unit in the residue field lifts to a square in the actual ring
of `p`-adic integers at every odd prime. The lifted residue root satisfies the
strict norm hypothesis of Hensel's lemma for `X^2-Q`. -/
theorem padicInt_isSquare_of_isSquare_residue_unit {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (Q : ℤ_[p])
    (hQ0 : PadicInt.toZMod Q ≠ 0) (hQ : IsSquare (PadicInt.toZMod Q)) :
    IsSquare Q := by
  obtain ⟨r, hr⟩ := hQ
  have hr0 : r ≠ 0 := by
    intro hz
    apply hQ0
    simpa [hz] using hr
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p] →+* ZMod p) r
  let F : Polynomial ℤ_[p] := X^2 - C Q
  have hval : F.aeval a = a^2 - Q := by simp [F]
  have hder : F.derivative.aeval a = 2*a := by norm_num [F]
  have hzero : PadicInt.toZMod (a^2-Q) = 0 := by
    simp only [map_sub, map_mul, ha, hr, pow_two, sub_self]
  have hsmall : ‖F.aeval a‖ < 1 := by
    rw [hval]
    exact (norm_lt_one_iff_residue_zero _).mpr hzero
  have hder0 : PadicInt.toZMod (2*a) ≠ 0 := by
    simpa only [map_mul, map_ofNat, ha] using mul_ne_zero (two_residue_ne_zero hp) hr0
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖^2 := by
    rw [hder, norm_eq_one_of_residue_ne_zero _ hder0, one_pow]
    exact hsmall
  obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
  have hz' : z^2 = Q := by simpa [F, sub_eq_zero] using hz
  exact ⟨z, by simpa only [pow_two] using hz'.symm⟩

/-- A nonzero square residue of an integer lifts to a square in Mathlib's
completed field `ℚ_[p]`, using the actual p-adic Hensel theorem. -/
theorem padic_isSquare_of_isSquare_zmod_unit {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (Q : ℤ) (hQ0 : ¬ (p : ℤ) ∣ Q)
    (hQ : IsSquare (Q : ZMod p)) : IsSquare (Q : ℚ_[p]) := by
  have hres : PadicInt.toZMod (Q : ℤ_[p]) ≠ 0 := by
    intro hz
    apply hQ0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd Q p).mp (by simpa only [map_intCast] using hz)
  obtain ⟨z, hz⟩ := padicInt_isSquare_of_isSquare_residue_unit hp (Q : ℤ_[p]) hres
    (by simpa only [map_intCast] using hQ)
  refine ⟨(z : ℚ_[p]), ?_⟩
  exact congrArg (fun v : ℤ_[p] => (v : ℚ_[p])) hz

/-- At an odd prime, a square root of two in the residue field lifts to a
square root of two in the actual p-adic field. -/
theorem padic_isSquare_two_of_isSquare_zmod {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (h2 : IsSquare (2 : ZMod p)) : IsSquare (2 : ℚ_[p]) := by
  have hunit : ¬ (p : ℤ) ∣ (2 : ℤ) := by
    intro hd
    have hd' : p ∣ 2 := by exact_mod_cast hd
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd')
  simpa only [Int.cast_ofNat] using padic_isSquare_of_isSquare_zmod_unit hp 2 hunit
    (by simpa only [Int.cast_ofNat] using h2)

end FourCorner

#print axioms FourCorner.padicInt_isSquare_of_isSquare_residue_unit
#print axioms FourCorner.padic_isSquare_two_of_isSquare_zmod
