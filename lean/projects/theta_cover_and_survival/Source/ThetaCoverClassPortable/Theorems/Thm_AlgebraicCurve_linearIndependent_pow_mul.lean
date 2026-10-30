import Mathlib.RingTheory.AlgebraTower
set_option autoImplicit false
namespace AlgebraicCurve
theorem linearIndependent_pow_mul {K E F : Type*} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    {x : E} {n : ℕ} {u : Fin n → F}
    (hx : LinearIndependent K (fun j : ℕ => x ^ j)) (hu : LinearIndependent E u) :
    LinearIndependent K (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2) := by
  have heq : (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2) =
      (fun p : ℕ × Fin n => (x ^ p.1) • u p.2) := by
    funext p
    rw [Algebra.smul_def,map_pow]
  rw [heq]
  exact linearIndependent_smul (R:=K) (S:=E) (A:=F) hx hu
end AlgebraicCurve
#print axioms AlgebraicCurve.linearIndependent_pow_mul
