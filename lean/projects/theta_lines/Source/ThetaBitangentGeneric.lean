import ThetaBitangentCore
import ThetaBitangentCases

namespace FourCorner

variable {K : Type*} [Field K] [CharZero K]

/-- A square restriction with both line coefficients nonzero cannot have its
cubic coefficient zero; this includes potential vanishing endpoint cases. -/
theorem theta_bitangent_generic_cubic_nonzero {α β : K}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : ThetaSquareCoefficients (thetaA4 α β) (thetaA3 α β)
      (thetaA2 α β) (thetaA1 α β) (thetaA0 α β)) :
    -39592 + 79968*α^2 ≠ 0 := by
  obtain ⟨k,a,b,c,hk,hd,h4,h3,h2,h1,h0⟩ := h
  intro hg
  have hs : α^2 = (101 : K)/204 := by linear_combination (1/79968 : K)*hg
  have h4val : thetaA4 α β = (2 : K)/51 := by
    unfold thetaA4
    rw [show α^4 = (α^2)^2 by ring, hs]
    norm_num
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide),mul_zero,h4val] at h4
    norm_num at h4
  have hb : b = 0 := by
    have he : (2*k*a)*b = 0 := by rw [← h3]; simp [thetaA3,hg]
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hk) ha)
  have heβ : (2*α*β)*(-39592+79968*β^2) = 0 := by
    simpa only [thetaA1,hb,mul_zero,zero_mul] using h1
  have hgβ : -39592+79968*β^2 = 0 :=
    (mul_eq_zero.mp heβ).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hα) hβ)
  have ht : β^2 = (101 : K)/204 := by linear_combination (1/79968 : K)*hgβ
  have h0val : thetaA0 α β = (2 : K)/51 := by
    unfold thetaA0
    rw [show β^4 = (β^2)^2 by ring, ht]
    norm_num
  have h2val : thetaA2 α β = (1999196 : K)/51 := by
    unfold thetaA2
    rw [hs,ht]
    norm_num
  have he : (thetaA2 α β)^2 = 4*(thetaA4 α β)*(thetaA0 α β) := by
    rw [h2,h4,h0,hb]
    ring
  rw [h4val,h0val,h2val] at he
  norm_num at he

/-- The two square-quartic elimination identities hold without an assumption
that either endpoint or either odd coefficient is nonzero. -/
theorem theta_bitangent_generic_invariants {α β : K}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : ThetaSquareCoefficients (thetaA4 α β) (thetaA3 α β)
      (thetaA2 α β) (thetaA1 α β) (thetaA0 α β)) :
    thetaBitangentI (α^2) (β^2) = 0 ∧ thetaBitangentII (α^2) (β^2) = 0 := by
  obtain ⟨k,a,b,c,hk,hd,h4,h3,h2,h1,h0⟩ := h
  have hi : (thetaA3 α β)^2*(thetaA0 α β) -
      (thetaA1 α β)^2*(thetaA4 α β) = 0 := by
    rw [h3,h0,h1,h4]
    ring
  have hii : (thetaA3 α β)^3 - 4*(thetaA4 α β)*(thetaA3 α β)*(thetaA2 α β) +
      8*(thetaA4 α β)^2*(thetaA1 α β) = 0 := by
    rw [h3,h4,h2,h1]
    ring
  have hc : 2*α*β ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hα) hβ
  constructor
  · have he : (thetaA3 α β)^2*(thetaA0 α β) -
        (thetaA1 α β)^2*(thetaA4 α β) =
        (2*α*β)^2 * thetaBitangentI (α^2) (β^2) := by
      unfold thetaA3 thetaA0 thetaA1 thetaA4 thetaBitangentI thetaBitangentF thetaBitangentG
      ring
    rw [he] at hi
    exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero 2 hc)
  · have he : (thetaA3 α β)^3 - 4*(thetaA4 α β)*(thetaA3 α β)*(thetaA2 α β) +
        8*(thetaA4 α β)^2*(thetaA1 α β) =
        (2*α*β) * thetaBitangentII (α^2) (β^2) := by
      unfold thetaA3 thetaA4 thetaA2 thetaA1 thetaBitangentII
        thetaBitangentF thetaBitangentG thetaBitangentH
      ring
    rw [he] at hii
    exact (mul_eq_zero.mp hii).resolve_left hc

/-- Complete necessity for the chart with two nonzero line coefficients. -/
theorem theta_bitangent_generic_four_cases {α β : K}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : ThetaSquareCoefficients (thetaA4 α β) (thetaA3 α β)
      (thetaA2 α β) (thetaA1 α β) (thetaA0 α β)) :
    (α^2 = 81/196 ∧ β^2 = 81/196) ∨
    (α^2 = 121/196 ∧ β^2 = 121/196) ∨
    (α^2 = 27/68 ∧ β^2 = 121/204) ∨
    (α^2 = 121/204 ∧ β^2 = 27/68) := by
  have hg : thetaBitangentG (α^2) ≠ 0 := theta_bitangent_generic_cubic_nonzero hα hβ h
  obtain ⟨hi,hii⟩ := theta_bitangent_generic_invariants hα hβ h
  exact thetaBitangent_equations_four_cases hi hii hg

#print axioms theta_bitangent_generic_cubic_nonzero
#print axioms theta_bitangent_generic_invariants
#print axioms theta_bitangent_generic_four_cases
end FourCorner
