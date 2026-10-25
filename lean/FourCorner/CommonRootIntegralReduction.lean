import FourCorner.CommonRootSource
import FourCorner.CommonRootPadicResidue

set_option autoImplicit false

namespace FourCorner
namespace CommonRootSource

variable {p : ℕ} [Fact p.Prime] {t : ℤ_[p]}

/-- A unit common parameter makes all four roots of the actual source
integral. Integrality follows in the completed field from the norm of each
square, rather than being imposed on the roots. -/
theorem integral_roots_of_unit (S : CommonRootSource ℚ_[p] (t : ℚ_[p]))
    (hell : ‖S.ell‖ = 1) :
    ‖S.P‖ ≤ 1 ∧ ‖S.C‖ ≤ 1 ∧ ‖S.M‖ ≤ 1 ∧ ‖S.B‖ ≤ 1 := by
  let e : ℤ_[p] := padicIntegral S.ell hell.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply padic_norm_le_one_of_sq (x := ((e + (t + 1) : ℤ_[p]) : ℚ_[p]))
      (e + (t + 1)).2
    exact S.sqP
  · apply padic_norm_le_one_of_sq (x := ((e - (t - 1) : ℤ_[p]) : ℚ_[p]))
      (e - (t - 1)).2
    exact S.sqC
  · apply padic_norm_le_one_of_sq (y := S.M) _ S.sqM
    rw [norm_div, norm_mul, hell, div_one]
    exact mul_le_one₀ (t - 1).2 (norm_nonneg _) ((t + 1) - e).2
  · apply padic_norm_le_one_of_sq (y := S.B) _ S.sqB
    rw [norm_div, norm_mul, hell, div_one]
    exact mul_le_one₀ (t + 1).2 (norm_nonneg _) (e + (t - 1)).2

/-- The four literal residue equations of an actual source with unit common
parameter. The residue roots are allowed to be zero. -/
theorem residue_equations_of_unit (S : CommonRootSource ℚ_[p] (t : ℚ_[p]))
    (hell : ‖S.ell‖ = 1) :
    let lam := padicResidue S.ell hell.le
    let τ := PadicInt.toZMod t
    let h := S.integral_roots_of_unit hell
    let P := padicResidue S.P h.1
    let C := padicResidue S.C h.2.1
    let M := padicResidue S.M h.2.2.1
    let B := padicResidue S.B h.2.2.2
    lam ≠ 0 ∧ P ^ 2 = lam + τ + 1 ∧ C ^ 2 = lam - τ + 1 ∧
      M ^ 2 = (τ - 1) * (τ + 1 - lam) / lam ∧
      B ^ 2 = (τ + 1) * (lam + τ - 1) / lam := by
  let e : ℤ_[p] := padicIntegral S.ell hell.le
  let P : ℤ_[p] := padicIntegral S.P (S.integral_roots_of_unit hell).1
  let C : ℤ_[p] := padicIntegral S.C (S.integral_roots_of_unit hell).2.1
  let M : ℤ_[p] := padicIntegral S.M (S.integral_roots_of_unit hell).2.2.1
  let B : ℤ_[p] := padicIntegral S.B (S.integral_roots_of_unit hell).2.2.2
  have he : PadicInt.toZMod e ≠ 0 :=
    (padicInt_norm_eq_one_iff_residue_ne_zero e).mp hell
  have hP : P ^ 2 = e + t + 1 := by
    apply PadicInt.ext
    change S.P ^ 2 = S.ell + (t : ℚ_[p]) + 1
    rw [S.sqP]
    ring
  have hC : C ^ 2 = e - t + 1 := by
    apply PadicInt.ext
    change S.C ^ 2 = S.ell - (t : ℚ_[p]) + 1
    rw [S.sqC]
    ring
  have hM : M ^ 2 * e = (t - 1) * (t + 1 - e) := by
    apply PadicInt.ext
    exact (eq_div_iff S.ell_ne_zero).mp S.sqM
  have hB : B ^ 2 * e = (t + 1) * (e + t - 1) := by
    apply PadicInt.ext
    change S.B ^ 2 * S.ell = ((t : ℚ_[p]) + 1) * (S.ell + (t : ℚ_[p]) - 1)
    rw [(eq_div_iff S.ell_ne_zero).mp S.sqB]
    ring
  change PadicInt.toZMod e ≠ 0 ∧ _
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · simpa only [map_pow, map_add, map_one, padicResidue, P, e] using
      congrArg (PadicInt.toZMod : ℤ_[p] →+* ZMod p) hP
  · simpa only [map_pow, map_sub, map_add, map_one, padicResidue, C, e] using
      congrArg (PadicInt.toZMod : ℤ_[p] →+* ZMod p) hC
  · apply (eq_div_iff he).mpr
    simpa only [map_pow, map_mul, map_sub, map_add, map_one, padicResidue, M, e] using
      congrArg (PadicInt.toZMod : ℤ_[p] →+* ZMod p) hM
  · apply (eq_div_iff he).mpr
    simpa only [map_pow, map_mul, map_sub, map_add, map_one, padicResidue, B, e] using
      congrArg (PadicInt.toZMod : ℤ_[p] →+* ZMod p) hB

/-- Every integral source with unit common parameter supplies all four square
conditions in its residue field, including possible zero radicands. -/
theorem residue_squares_of_unit (S : CommonRootSource ℚ_[p] (t : ℚ_[p]))
    (hell : ‖S.ell‖ = 1) :
    let lam := padicResidue S.ell hell.le
    let τ := PadicInt.toZMod t
    lam ≠ 0 ∧ IsSquare (lam + τ + 1) ∧ IsSquare (lam - τ + 1) ∧
      IsSquare ((τ - 1) * (τ + 1 - lam) / lam) ∧
      IsSquare ((τ + 1) * (lam + τ - 1) / lam) := by
  obtain ⟨he, hP, hC, hM, hB⟩ := S.residue_equations_of_unit hell
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact ⟨_, by simpa only [pow_two] using hP.symm⟩
    | exact ⟨_, by simpa only [pow_two] using hC.symm⟩
    | exact ⟨_, by simpa only [pow_two] using hM.symm⟩
    | exact ⟨_, by simpa only [pow_two] using hB.symm⟩

end CommonRootSource
end FourCorner

#print axioms FourCorner.CommonRootSource.integral_roots_of_unit
#print axioms FourCorner.CommonRootSource.residue_equations_of_unit
#print axioms FourCorner.CommonRootSource.residue_squares_of_unit
