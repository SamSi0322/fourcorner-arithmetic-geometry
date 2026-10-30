import ThetaCoverClassPortable.DoubleRootPolynomial
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

noncomputable section
set_option autoImplicit false
namespace FourCorner.BinaryQuarticDoubleRoots
open Polynomial
variable {K : Type*} [Field K]
abbrev Binary (K : Type*) [Field K] := MvPolynomial (Fin 2) K

def dehom (F : Binary K) : K[X] := MvPolynomial.aeval ![X, 1] F

/-- The genuine homogenization inverse supplies coefficient-level injectivity,
including over finite fields. No equality-of-functions shortcut is used. -/
theorem recover (F : Binary K) {n : ℕ} (hF : F.IsHomogeneous n) :
    (dehom F).homogenize n = F :=
  Polynomial.homogenize_eq_of_isHomogeneous hF rfl

theorem dehom_injective {F G : Binary K} {n : ℕ}
    (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous n) (h : dehom F = dehom G) : F = G := by
  calc
    F = (dehom F).homogenize n := (recover F hF).symm
    _ = (dehom G).homogenize n := congrArg (fun p : K[X] => p.homogenize n) h
    _ = G := recover G hG

theorem dehom_ne_zero {F : Binary K} {n : ℕ} (hF : F.IsHomogeneous n) (hf : F ≠ 0) :
    dehom F ≠ 0 := by
  intro h
  have hh := recover F hF
  rw [h, homogenize_zero] at hh
  exact hf hh.symm

private theorem exponent_sum {F : Binary K} {n : ℕ} (hF : F.IsHomogeneous n)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ F.support) : d 0 + d 1 = n := by
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using
    hF (MvPolynomial.mem_support_iff.mp hd)

theorem dehom_degree {F : Binary K} {n : ℕ} (hF : F.IsHomogeneous n) :
    (dehom F).natDegree ≤ n := by
  classical
  unfold dehom
  rw [F.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hh := exponent_sum hF hd
  simp only [MvPolynomial.aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_pow, mul_one, Algebra.algebraMap_self, RingHom.id_apply]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp; omega)

theorem dehom_eval (F : Binary K) (u : K) :
    (dehom F).eval u = MvPolynomial.aeval ![u, 1] F := by
  have hh : (Polynomial.aeval u).comp (MvPolynomial.aeval ![X, 1]) =
      (MvPolynomial.aeval ![u, 1] : Binary K →ₐ[K] K) := by
    ext i
    fin_cases i <;> simp
  exact DFunLike.congr_fun hh F

theorem derivative_dehom (F : Binary K) :
    (dehom F).derivative = dehom (MvPolynomial.pderiv 0 F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [dehom]
  | add p q hp hq => simpa only [dehom, map_add, Polynomial.derivative_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    fin_cases i <;> simp_all [dehom, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
      Polynomial.derivative_mul, Pi.single_apply] <;> ring

/-- Evaluation of every homogeneous binary polynomial scales with its actual degree. -/
theorem eval_scale {F : Binary K} {n : ℕ} (hF : F.IsHomogeneous n)
    (a : K) (v : Fin 2 → K) :
    MvPolynomial.aeval (a • v) F = a^n * MvPolynomial.aeval v F := by
  classical
  rw [F.as_sum, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hh := exponent_sum hF hd
  simp [MvPolynomial.aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two,
    Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← hh, pow_add]
  ring

/-- A fully explicit expression for the real homogeneous quartic, from its dehomogenization. -/
theorem homogenize_four (p : K[X]) : p.homogenize 4 =
    MvPolynomial.C (p.coeff 4) * MvPolynomial.X 0^4 +
    MvPolynomial.C (p.coeff 3) * MvPolynomial.X 0^3 * MvPolynomial.X 1 +
    MvPolynomial.C (p.coeff 2) * MvPolynomial.X 0^2 * MvPolynomial.X 1^2 +
    MvPolynomial.C (p.coeff 1) * MvPolynomial.X 0 * MvPolynomial.X 1^3 +
    MvPolynomial.C (p.coeff 0) * MvPolynomial.X 1^4 := by
  rw [Polynomial.homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, MvPolynomial.monomial_eq, Finsupp.prod_fintype,
    Fin.prod_univ_two]
  ring

end FourCorner.BinaryQuarticDoubleRoots
