import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace FourCorner

/-- If an integer is a square in the actual `p`-adic field, its residue is a square.
The root has norm at most one, so it belongs to the `p`-adic integers and can be
mapped through the residue ring homomorphism. -/
theorem isSquare_zmod_of_isSquare_padic {p : ℕ} [Fact p.Prime] (Q : ℤ)
    (hQ : IsSquare (Q : ℚ_[p])) : IsSquare (Q : ZMod p) := by
  obtain ⟨x, hx⟩ := hQ
  have hnorm : ‖x‖ ≤ 1 := by
    have hsq : ‖x‖ * ‖x‖ ≤ 1 := by
      rw [← norm_mul, ← hx]
      exact Padic.norm_int_le_one Q
    nlinarith [norm_nonneg x]
  let y : ℤ_[p] := ⟨x, hnorm⟩
  have hy : (Q : ℤ_[p]) = y * y := by
    apply PadicInt.ext
    exact hx
  have hred := congrArg (PadicInt.toZMod : ℤ_[p] →+* ZMod p) hy
  refine ⟨PadicInt.toZMod y, ?_⟩
  simpa only [map_intCast, map_mul] using hred

/-- A nonsquare residue obstructs an integer from being a square in `ℚ_[p]`. -/
theorem not_isSquare_padic_of_not_isSquare_zmod {p : ℕ} [Fact p.Prime] (Q : ℤ)
    (hQ : ¬ IsSquare (Q : ZMod p)) : ¬ IsSquare (Q : ℚ_[p]) :=
  fun h => hQ (isSquare_zmod_of_isSquare_padic Q h)

private instance prime17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The obstruction at seventeen is stated in Mathlib's completed field `ℚ_[17]`. -/
theorem genuineQ17_nonsquare_of_residue (Q : ℤ)
    (hQ : ¬ IsSquare (Q : ZMod 17)) : ¬ IsSquare (Q : ℚ_[17]) :=
  not_isSquare_padic_of_not_isSquare_zmod Q hQ

/-- Dividing an integer by a nonzero integer square preserves the obstruction. -/
theorem genuineQ17_div_sq_nonsquare_of_residue (Q D : ℤ) (hD : D ≠ 0)
    (hQ : ¬ IsSquare (Q : ZMod 17)) :
    ¬ IsSquare ((Q : ℚ_[17]) / (D : ℚ_[17]) ^ 2) := by
  intro hs
  have hD' : (D : ℚ_[17]) ≠ 0 := by exact_mod_cast hD
  have h := hs.mul (IsSquare.sq (D : ℚ_[17]))
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hD')] at h
  exact genuineQ17_nonsquare_of_residue Q hQ h

end FourCorner
