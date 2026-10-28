import ThetaBitangentQuadraticIndependence
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Star.Rat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace FourCorner

open scoped QuadraticAlgebra

/-- The two literal radical generators in the genuine degree-four field. -/
def thetaGaloisR : ThetaBiquadratic := ⟨(ω : ThetaSqrtTwo), 0⟩
def thetaGaloisS : ThetaBiquadratic := ω

/-- The sign change of sqrt(2), fixing sqrt(51), as a field algebra automorphism. -/
def thetaFlipTwo : ThetaBiquadratic ≃ₐ[ℚ] ThetaBiquadratic where
  toFun z := ⟨star z.re, star z.im⟩
  invFun z := ⟨star z.re, star z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by
    apply QuadraticAlgebra.ext <;> simp [star_mul, mul_comm]
  map_add' z w := by
    apply QuadraticAlgebra.ext <;> simp
  commutes' q := by
    apply QuadraticAlgebra.ext
    · change star (algebraMap ℚ ThetaSqrtTwo q) = algebraMap ℚ ThetaSqrtTwo q
      ext <;> simp
    · simp

/-- The sign change of sqrt(51), fixing sqrt(2). -/
def thetaFlipFiftyone : ThetaBiquadratic ≃ₐ[ℚ] ThetaBiquadratic where
  toFun z := ⟨z.re, -z.im⟩
  invFun z := ⟨z.re, -z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by ext <;> simp <;> ring
  map_add' z w := by ext <;> simp <;> ring
  commutes' q := by ext <;> simp

@[simp] theorem thetaGaloisR_sq : thetaGaloisR ^ 2 = 2 := by
  ext <;> simp [thetaGaloisR, pow_two, QuadraticAlgebra.omega] <;> norm_num

@[simp] theorem thetaGaloisS_sq : thetaGaloisS ^ 2 = 51 := by
  ext <;> simp [thetaGaloisS, pow_two, QuadraticAlgebra.omega] <;> norm_num

@[simp] theorem thetaFlipTwo_R : thetaFlipTwo thetaGaloisR = -thetaGaloisR := by
  ext <;> simp [thetaFlipTwo, thetaGaloisR, QuadraticAlgebra.omega]

@[simp] theorem thetaFlipTwo_S : thetaFlipTwo thetaGaloisS = thetaGaloisS := by
  ext <;> simp [thetaFlipTwo, thetaGaloisS, QuadraticAlgebra.omega]

@[simp] theorem thetaFlipFiftyone_R : thetaFlipFiftyone thetaGaloisR = thetaGaloisR := by
  ext <;> simp [thetaFlipFiftyone, thetaGaloisR, QuadraticAlgebra.omega]

@[simp] theorem thetaFlipFiftyone_S : thetaFlipFiftyone thetaGaloisS = -thetaGaloisS := by
  ext <;> simp [thetaFlipFiftyone, thetaGaloisS, QuadraticAlgebra.omega]

/-- Every element has its literal four rational coordinates in the radical basis. -/
theorem theta_biquadratic_coordinates (z : ThetaBiquadratic) :
    z = algebraMap ℚ _ z.re.re + algebraMap ℚ _ z.re.im * thetaGaloisR +
      algebraMap ℚ _ z.im.re * thetaGaloisS +
      algebraMap ℚ _ z.im.im * thetaGaloisR * thetaGaloisS := by
  ext <;> simp [thetaGaloisR, thetaGaloisS, QuadraticAlgebra.omega]

/-- Equality on the two actual radical generators determines a rational algebra map. -/
theorem theta_biquadratic_algHom_ext {F : Type*} [CommRing F] [Algebra ℚ F]
    (f g : ThetaBiquadratic →ₐ[ℚ] F)
    (hr : f thetaGaloisR = g thetaGaloisR)
    (hs : f thetaGaloisS = g thetaGaloisS) : f = g := by
  ext z
  rw [theta_biquadratic_coordinates z]
  simp only [map_add, map_mul, AlgHom.commutes, hr, hs]

/-- The two independent sign changes commute on actual field elements. -/
theorem theta_sign_changes_commute :
    thetaFlipTwo.trans thetaFlipFiftyone = thetaFlipFiftyone.trans thetaFlipTwo := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply theta_biquadratic_algHom_ext <;> simp

/-- Each rational automorphism sends each radical to one of its two actual roots. -/
theorem theta_aut_radical_signs (σ : ThetaBiquadratic ≃ₐ[ℚ] ThetaBiquadratic) :
    (σ thetaGaloisR = thetaGaloisR ∨ σ thetaGaloisR = -thetaGaloisR) ∧
    (σ thetaGaloisS = thetaGaloisS ∨ σ thetaGaloisS = -thetaGaloisS) := by
  constructor
  · apply (sq_eq_sq_iff_eq_or_eq_neg).mp
    rw [← map_pow, thetaGaloisR_sq, map_ofNat]
  · apply (sq_eq_sq_iff_eq_or_eq_neg).mp
    rw [← map_pow, thetaGaloisS_sq, map_ofNat]

/-- These four genuine algebra automorphisms exhaust the Galois action on K. -/
theorem theta_aut_four_cases (σ : ThetaBiquadratic ≃ₐ[ℚ] ThetaBiquadratic) :
    σ = AlgEquiv.refl ∨ σ = thetaFlipTwo ∨ σ = thetaFlipFiftyone ∨
      σ = thetaFlipTwo.trans thetaFlipFiftyone := by
  rcases theta_aut_radical_signs σ with ⟨hr | hr, hs | hs⟩
  · left
    apply AlgEquiv.coe_toAlgHom_injective
    apply theta_biquadratic_algHom_ext <;> simpa
  · right; right; left
    apply AlgEquiv.coe_toAlgHom_injective
    apply theta_biquadratic_algHom_ext <;> simpa
  · right; left
    apply AlgEquiv.coe_toAlgHom_injective
    apply theta_biquadratic_algHom_ext <;> simpa
  · right; right; right
    apply AlgEquiv.coe_toAlgHom_injective
    apply theta_biquadratic_algHom_ext <;> simpa

#print axioms theta_aut_four_cases
#print axioms theta_sign_changes_commute

/-- The concrete splitting field has degree four over Q. -/
theorem theta_biquadratic_degree_four : Module.finrank ℚ ThetaBiquadratic = 4 := by
  rw [← Module.finrank_mul_finrank ℚ ThetaSqrtTwo ThetaBiquadratic,
    QuadraticAlgebra.finrank_eq_two, QuadraticAlgebra.finrank_eq_two]

#print axioms theta_biquadratic_degree_four
end FourCorner
