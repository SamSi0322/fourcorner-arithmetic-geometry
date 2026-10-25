import FourCorner.RadiusModel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace FourCorner

/-- An actual ordered point of the affine four-root curve. Every removed
coordinate and parameter value is explicitly excluded. -/
structure CommonRootSource (K : Type*) [Field K] (t : K) where
  ell : K
  P : K
  C : K
  M : K
  B : K
  t_ne_zero : t ≠ 0
  t_ne_one : t ≠ 1
  t_ne_neg_one : t ≠ -1
  ell_ne_zero : ell ≠ 0
  P_ne_zero : P ≠ 0
  C_ne_zero : C ≠ 0
  M_ne_zero : M ≠ 0
  B_ne_zero : B ≠ 0
  sqP : P^2 = ell + (t+1)
  sqC : C^2 = ell - (t-1)
  sqM : M^2 = (t-1) * ((t+1)-ell) / ell
  sqB : B^2 = (t+1) * (ell+(t-1)) / ell

namespace CommonRootSource

variable {K : Type*} [Field K] {t : K}

theorem s_ne_zero (S : CommonRootSource K t) : t-1 ≠ 0 := sub_ne_zero.mpr S.t_ne_one

theorem T_ne_zero (S : CommonRootSource K t) : t+1 ≠ 0 := by
  intro h
  exact S.t_ne_neg_one (eq_neg_of_add_eq_zero_left h)

theorem d_ne_zero (S : CommonRootSource K t) : t^2-1 ≠ 0 := by
  rw [show t^2-1=(t-1)*(t+1) by ring]
  exact mul_ne_zero S.s_ne_zero S.T_ne_zero

theorem T_sub_ell_ne_zero (S : CommonRootSource K t) : t+1-S.ell ≠ 0 := by
  intro he
  have hs := S.sqM
  rw [he,mul_zero,zero_div] at hs
  exact S.M_ne_zero (sq_eq_zero_iff.mp hs)

theorem ell_add_s_ne_zero (S : CommonRootSource K t) : S.ell+(t-1) ≠ 0 := by
  intro he
  have hs := S.sqB
  rw [he,mul_zero,zero_div] at hs
  exact S.B_ne_zero (sq_eq_zero_iff.mp hs)

theorem ell_sub_s_ne_zero (S : CommonRootSource K t) : S.ell-(t-1) ≠ 0 := by
  rw [← S.sqC]
  exact pow_ne_zero 2 S.C_ne_zero

theorem ell_add_T_ne_zero (S : CommonRootSource K t) : S.ell+(t+1) ≠ 0 := by
  rw [← S.sqP]
  exact pow_ne_zero 2 S.P_ne_zero

end CommonRootSource
end FourCorner
