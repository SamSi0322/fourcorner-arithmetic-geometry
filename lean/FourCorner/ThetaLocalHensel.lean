import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic

namespace FourCorner

open Polynomial

/-- The quadratic principal-unit criterion, proved by Hensel's lemma at `1`. -/
theorem padicInt_isSquare_one_add {p : ℕ} [Fact p.Prime] (t : ℤ_[p])
    (ht : ‖t‖ < ‖(2 : ℤ_[p])‖ ^ 2) : IsSquare (1 + t) := by
  let F : Polynomial ℤ_[p] := X ^ 2 - C (1 + t)
  have hval : F.aeval (1 : ℤ_[p]) = -t := by simp [F]
  have hder : F.derivative.aeval (1 : ℤ_[p]) = 2 := by norm_num [F]
  have hnorm : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    simpa [hval, hder] using ht
  obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
  have hz' : z ^ 2 = 1 + t := by
    simpa [F, sub_eq_zero] using hz
  exact ⟨z, by simpa [pow_two] using hz'.symm⟩

/-- Every sufficiently small perturbation of one is a square in the actual field `ℚ_[p]`.
The root is obtained in `ℤ_[p]` from Hensel's lemma. -/
theorem padic_isSquare_one_add {p : ℕ} [Fact p.Prime] (t : ℚ_[p])
    (ht : ‖t‖ < ‖(2 : ℚ_[p])‖ ^ 2) : IsSquare (1 + t) := by
  have htwo : ‖(2 : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one 2
  have htone : ‖t‖ ≤ 1 := by nlinarith [norm_nonneg (2 : ℚ_[p])]
  let u : ℤ_[p] := ⟨t, htone⟩
  have hu : ‖u‖ < ‖(2 : ℤ_[p])‖ ^ 2 := by
    change ‖t‖ < ‖(2 : ℚ_[p])‖ ^ 2
    exact ht
  obtain ⟨z, hz⟩ := padicInt_isSquare_one_add u hu
  refine ⟨(z : ℚ_[p]), ?_⟩
  have h := congrArg (fun v : ℤ_[p] => (v : ℚ_[p])) hz
  exact h

/-- At an odd prime the usual open unit ball suffices. -/
theorem padic_odd_isSquare_one_add {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (t : ℚ_[p]) (ht : ‖t‖ < 1) : IsSquare (1 + t) := by
  have htwo : ‖(2 : ℚ_[p])‖ = 1 := by
    apply Padic.norm_natCast_eq_one_iff.mpr
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
      intro h
      exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h))
  apply padic_isSquare_one_add t
  simpa [htwo] using ht

/-- The dyadic principal-unit criterion with the explicit radius `1/4`. -/
theorem padic_two_isSquare_one_add (t : ℚ_[2]) (ht : ‖t‖ < 1 / 4) :
    IsSquare (1 + t) := by
  apply padic_isSquare_one_add t
  have htwo : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
    simpa using (Padic.norm_p (p := 2))
  rw [htwo]
  norm_num
  exact ht

end FourCorner

#print axioms FourCorner.padicInt_isSquare_one_add
#print axioms FourCorner.padic_isSquare_one_add
#print axioms FourCorner.padic_odd_isSquare_one_add
#print axioms FourCorner.padic_two_isSquare_one_add
