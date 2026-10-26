import CriticalProj23
import CriticalElliptic23
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Literal homogeneous ideal and Jacobian bridge for the actual Proj critical curve. -/
noncomputable section
set_option autoImplicit false
namespace FourCorner.CriticalProj23
open MvPolynomial CriticalElliptic23
variable {k : Type*} [Field k]

theorem equations_eval_iff (i : k) (v : Fin 4 → k) :
    (eval v (F0 i) = 0 ∧ eval v (F1 i) = 0) ↔ CriticalCoordinates i v := by
  simp only [F0,F1,map_sub,map_pow,map_mul,eval_X,eval_C,CriticalCoordinates,Shift]
  exact and_congr sub_eq_zero sub_eq_zero

theorem criticalIdeal_le_eval_kernel (i : k) (v : Fin 4 → k) :
    criticalIdeal i ≤ RingHom.ker (eval v) ↔ CriticalCoordinates i v := by
  rw [criticalIdeal,Ideal.span_le]
  constructor
  · intro h
    apply (equations_eval_iff i v).mp
    exact ⟨h ⟨0,rfl⟩,h ⟨1,rfl⟩⟩
  · intro h p hp
    rcases hp with ⟨j,rfl⟩
    have he := (equations_eval_iff i v).mpr h
    fin_cases j
    · exact he.1
    · exact he.2

theorem eval_pderiv_F0 (i : k) (v : Fin 4 → k) (j : Fin 4) :
    eval v (pderiv j (F0 i)) = 2 * ![(i-1)*v 0,-i*v 1,v 2,0] j := by
  fin_cases j <;> simp [F0] <;> ring

theorem eval_pderiv_F1 (i : k) (v : Fin 4 → k) (j : Fin 4) :
    eval v (pderiv j (F1 i)) = 2 * ![i*v 0,-(1+i)*v 1,0,v 3] j := by
  fin_cases j <;> simp [F1] <;> ring

/-- The actual polynomial Jacobian has no nonzero linear relation at any nonzero
critical cone point, over every field extension with the same hypotheses. -/
theorem jacobian_kernel_trivial (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (v : Fin 4 → k) (hc : CriticalCoordinates i v) (hn : ∃ j, v j ≠ 0)
    (l m : k) (hg : ∀ j, l*eval v (pderiv j (F0 i)) +
      m*eval v (pderiv j (F1 i)) = 0) : l = 0 ∧ m = 0 := by
  have hh : ∀ j, l*(2 * ![(i-1)*v 0,-i*v 1,v 2,0] j) +
      m*(2 * ![i*v 0,-(1+i)*v 1,0,v 3] j) = 0 := by
    simpa only [eval_pderiv_F0,eval_pderiv_F1] using hg
  apply pencil_kernel_trivial i hi h2 v hc hn l m
  · apply (mul_eq_zero.mp (show 2 * (((i-1)*l+i*m)*v 0) = 0 from by
      have h := hh 0
      simp only [Matrix.cons_val_zero] at h
      linear_combination h)).resolve_left h2
  · apply (mul_eq_zero.mp (show 2 * ((-i*l-(1+i)*m)*v 1) = 0 from by
      have h := hh 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
      linear_combination h)).resolve_left h2
  · apply (mul_eq_zero.mp (show 2 * (l*v 2) = 0 from by
      have h := hh 2
      change l*(2*v 2)+m*(2*0) = 0 at h
      linear_combination h)).resolve_left h2
  · apply (mul_eq_zero.mp (show 2 * (m*v 3) = 0 from by
      have h := hh 3
      change l*(2*0)+m*(2*v 3) = 0 at h
      linear_combination h)).resolve_left h2

#print axioms equations_eval_iff
#print axioms criticalIdeal_le_eval_kernel
#print axioms jacobian_kernel_trivial
end FourCorner.CriticalProj23
