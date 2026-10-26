import HasseRationalBranchFiniteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

noncomputable section
set_option autoImplicit false
namespace FourCorner.HasseMatrixBranchFiniteness
open ProjectiveThreePoint HasseBranchConfiguration
variable {K:Type*} [Field K]

/-- The native equivalence from ALL invertible 2x2 matrices to all linear
automorphisms of the native two-dimensional coordinate space. -/
def matrixLinearEquiv:Matrix.GeneralLinearGroup (Fin 2) K≃*(V K≃ₗ[K]V K):=
 Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K (V K))

def MatrixEquivalent (h2:(2:K)≠0) (p q:K):Prop:=
 ∃g:Matrix.GeneralLinearGroup (Fin 2) K,
  action (matrixLinearEquiv g) '' branchSet h2 p=branchSet h2 q

theorem matrixEquivalent_iff (h2:(2:K)≠0) (p q:K):
 MatrixEquivalent h2 p q ↔Equivalent h2 p q:=by
 constructor
 · rintro ⟨g,hg⟩;exact ⟨matrixLinearEquiv g,hg⟩
 · rintro ⟨h,hh⟩
   obtain ⟨g,hg⟩:=matrixLinearEquiv.surjective h
   exact ⟨g,by rw [hg];exact hh⟩

theorem finite_matrix_fibre (h2:(2:K)≠0) (q:K):
 {p:K|MatrixEquivalent h2 p q}.Finite:=
 (finite_parameter_fibre h2 q).subset (by intro p hp;exact (matrixEquivalent_iff h2 p q).mp hp)

variable [CharZero K]
theorem finite_rational_matrix_fibre (q:ℚ):
 {p:ℚ|1<p ∧MatrixEquivalent (K:=K) (by norm_num) (p:K) (q:K)}.Finite:=by
 apply (HasseRationalBranchFiniteness.finite_positive_rational_fibre (K:=K) q).subset
 intro p hp
 exact ⟨hp.1,(matrixEquivalent_iff _ _ _).mp hp.2⟩

#print axioms matrixEquivalent_iff
#print axioms finite_matrix_fibre
#print axioms finite_rational_matrix_fibre
end FourCorner.HasseMatrixBranchFiniteness
