import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace FourCorner

/-- A square root of an integral `p`-adic number is integral. -/
theorem padic_norm_le_one_of_sq {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : y ^ 2 = x) : ‖y‖ ≤ 1 := by
  have hnorm : ‖y‖ ^ 2 = ‖x‖ := by rw [← norm_pow, hy]
  nlinarith [norm_nonneg y]

/-- An integral element is a square in the `p`-adic field exactly when it is
already a square in the `p`-adic integer ring. -/
theorem padicInt_isSquare_coe_iff {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    IsSquare (x : ℚ_[p]) ↔ IsSquare x := by
  constructor
  · rintro ⟨y, hy⟩
    have hyint : ‖y‖ ≤ 1 :=
      padic_norm_le_one_of_sq x.2 (by simpa only [pow_two] using hy.symm)
    refine ⟨⟨y, hyint⟩, ?_⟩
    apply PadicInt.ext
    exact hy
  · exact IsSquare.map PadicInt.Coe.ringHom

/-- Any square in the `p`-adic field which is integral has square residue. -/
theorem padicInt_isSquare_toZMod_of_isSquare_coe {p : ℕ} [Fact p.Prime]
    (x : ℤ_[p]) (hx : IsSquare (x : ℚ_[p])) :
    IsSquare (PadicInt.toZMod x) :=
  IsSquare.map PadicInt.toZMod ((padicInt_isSquare_coe_iff x).mp hx)

end FourCorner

#print axioms FourCorner.padic_norm_le_one_of_sq
#print axioms FourCorner.padicInt_isSquare_coe_iff
#print axioms FourCorner.padicInt_isSquare_toZMod_of_isSquare_coe
