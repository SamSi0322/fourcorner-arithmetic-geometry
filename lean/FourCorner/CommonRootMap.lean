import FourCorner.CommonRootSource
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace FourCorner.CommonRootSource

/-- Base change of the exact ordered rational source to the actual completed
p-adic field, retaining every nonzero coordinate and every root equation. -/
noncomputable def toPadic {t : ℚ} (S : CommonRootSource ℚ t) (p : ℕ) [Fact p.Prime] :
    CommonRootSource ℚ_[p] (t : ℚ_[p]) where
  ell := S.ell
  P := S.P
  C := S.C
  M := S.M
  B := S.B
  t_ne_zero := by exact_mod_cast S.t_ne_zero
  t_ne_one := by exact_mod_cast S.t_ne_one
  t_ne_neg_one := by exact_mod_cast S.t_ne_neg_one
  ell_ne_zero := by exact_mod_cast S.ell_ne_zero
  P_ne_zero := by exact_mod_cast S.P_ne_zero
  C_ne_zero := by exact_mod_cast S.C_ne_zero
  M_ne_zero := by exact_mod_cast S.M_ne_zero
  B_ne_zero := by exact_mod_cast S.B_ne_zero
  sqP := by exact_mod_cast S.sqP
  sqC := by exact_mod_cast S.sqC
  sqM := by exact_mod_cast S.sqM
  sqB := by exact_mod_cast S.sqB

@[simp] theorem toPadic_ell {t : ℚ} (S : CommonRootSource ℚ t) (p : ℕ) [Fact p.Prime] :
    (S.toPadic p).ell = (S.ell : ℚ_[p]) := rfl

end FourCorner.CommonRootSource
