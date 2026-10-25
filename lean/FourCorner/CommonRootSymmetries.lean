import FourCorner.CommonRootSource
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace FourCorner
namespace CommonRootSource

variable {K : Type*} [Field K] {t : K}

/-- The five affine coordinates determine an actual common-root source. -/
@[ext] theorem ext {S R : CommonRootSource K t}
    (hell : S.ell = R.ell) (hP : S.P = R.P) (hC : S.C = R.C)
    (hM : S.M = R.M) (hB : S.B = R.B) : S = R := by
  cases S
  cases R
  simp_all

/-- Reflection exchanges the two pairs of actual square roots and sends
`ell` to `(t²-1)/ell`. All removed coordinates remain nonzero. -/
def reflect (S : CommonRootSource K t) : CommonRootSource K t where
  ell := (t^2-1)/S.ell
  P := S.B
  C := S.M
  M := S.C
  B := S.P
  t_ne_zero := S.t_ne_zero
  t_ne_one := S.t_ne_one
  t_ne_neg_one := S.t_ne_neg_one
  ell_ne_zero := div_ne_zero S.d_ne_zero S.ell_ne_zero
  P_ne_zero := S.B_ne_zero
  C_ne_zero := S.M_ne_zero
  M_ne_zero := S.C_ne_zero
  B_ne_zero := S.P_ne_zero
  sqP := by
    rw [S.sqB]
    field_simp [S.ell_ne_zero]
    ring
  sqC := by
    rw [S.sqM]
    field_simp [S.ell_ne_zero]
    ring
  sqM := by
    rw [S.sqC]
    field_simp [S.ell_ne_zero, S.d_ne_zero]
    ring
  sqB := by
    rw [S.sqP]
    field_simp [S.ell_ne_zero, S.d_ne_zero]
    ring

@[simp] theorem reflect_ell (S : CommonRootSource K t) :
    S.reflect.ell = (t^2-1)/S.ell := rfl
@[simp] theorem reflect_P (S : CommonRootSource K t) : S.reflect.P = S.B := rfl
@[simp] theorem reflect_C (S : CommonRootSource K t) : S.reflect.C = S.M := rfl
@[simp] theorem reflect_M (S : CommonRootSource K t) : S.reflect.M = S.C := rfl
@[simp] theorem reflect_B (S : CommonRootSource K t) : S.reflect.B = S.P := rfl

@[simp] theorem reflect_reflect (S : CommonRootSource K t) : S.reflect.reflect = S := by
  apply ext
  · simp only [reflect_ell]
    field_simp [S.ell_ne_zero, S.d_ne_zero]
  all_goals rfl

/-- Changing the sign of `t` preserves `ell` and exchanges the actual roots
within each pair. -/
def signChange (S : CommonRootSource K t) : CommonRootSource K (-t) where
  ell := S.ell
  P := S.C
  C := S.P
  M := S.B
  B := S.M
  t_ne_zero := neg_ne_zero.mpr S.t_ne_zero
  t_ne_one := by
    intro h
    apply S.t_ne_neg_one
    linear_combination -h
  t_ne_neg_one := by
    intro h
    apply S.t_ne_one
    linear_combination -h
  ell_ne_zero := S.ell_ne_zero
  P_ne_zero := S.C_ne_zero
  C_ne_zero := S.P_ne_zero
  M_ne_zero := S.B_ne_zero
  B_ne_zero := S.M_ne_zero
  sqP := by rw [S.sqC]; ring
  sqC := by rw [S.sqP]; ring
  sqM := by rw [S.sqB]; congr 1; ring
  sqB := by rw [S.sqM]; congr 1; ring

@[simp] theorem signChange_ell (S : CommonRootSource K t) : S.signChange.ell = S.ell := rfl
@[simp] theorem signChange_P (S : CommonRootSource K t) : S.signChange.P = S.C := rfl
@[simp] theorem signChange_C (S : CommonRootSource K t) : S.signChange.C = S.P := rfl
@[simp] theorem signChange_M (S : CommonRootSource K t) : S.signChange.M = S.B := rfl
@[simp] theorem signChange_B (S : CommonRootSource K t) : S.signChange.B = S.M := rfl

/-- Transport only the parameter index; all affine coordinates are retained. -/
def reparam {u : K} (h : t = u) (S : CommonRootSource K t) : CommonRootSource K u := h ▸ S

@[simp] theorem reparam_ell {u : K} (h : t = u) (S : CommonRootSource K t) :
    (S.reparam h).ell = S.ell := by cases h; rfl
@[simp] theorem reparam_P {u : K} (h : t = u) (S : CommonRootSource K t) :
    (S.reparam h).P = S.P := by cases h; rfl
@[simp] theorem reparam_C {u : K} (h : t = u) (S : CommonRootSource K t) :
    (S.reparam h).C = S.C := by cases h; rfl
@[simp] theorem reparam_M {u : K} (h : t = u) (S : CommonRootSource K t) :
    (S.reparam h).M = S.M := by cases h; rfl
@[simp] theorem reparam_B {u : K} (h : t = u) (S : CommonRootSource K t) :
    (S.reparam h).B = S.B := by cases h; rfl

@[simp] theorem signChange_signChange (S : CommonRootSource K t) :
    (S.signChange.signChange).reparam (neg_neg t) = S := by
  apply ext <;> simp

/-- The two involutions commute on the entire source, including its roots. -/
theorem reflect_signChange (S : CommonRootSource K t) :
    S.reflect.signChange = S.signChange.reflect := by
  apply ext <;> simp

/-- Exact multiplicative square-class witness for reflection. -/
theorem reflect_ell_square_witness (S : CommonRootSource K t) :
    S.reflect.ell = ((t^2-1)*S.ell) * (S.ell⁻¹)^2 := by
  rw [reflect_ell]
  field_simp [S.ell_ne_zero]

/-- The reflection multiplies the square class of `ell` by that of `t²-1`. -/
theorem reflect_ell_square_class (S : CommonRootSource K t) :
    ∃ u : K, u ≠ 0 ∧ S.reflect.ell = ((t^2-1)*S.ell)*u^2 :=
  ⟨S.ell⁻¹, inv_ne_zero S.ell_ne_zero, S.reflect_ell_square_witness⟩

end CommonRootSource
end FourCorner
#print axioms FourCorner.CommonRootSource.reflect
#print axioms FourCorner.CommonRootSource.signChange
#print axioms FourCorner.CommonRootSource.reflect_reflect
#print axioms FourCorner.CommonRootSource.signChange_signChange
#print axioms FourCorner.CommonRootSource.reflect_signChange
#print axioms FourCorner.CommonRootSource.reflect_ell_square_class
