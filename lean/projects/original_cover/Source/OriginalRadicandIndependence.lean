import geometry.SquarefreeRatFunc
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

/-! The four literal original radicands have independent square classes in the
actual two-variable rational function field, over every characteristic-zero field. -/
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
noncomputable section
namespace FourCorner.OriginalCoverCompletion.OriginalRadicands
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

def f (x : K) : Fin 4 → K[X]
 | 0 => X^2+C (x^2)
 | 1 => X^2+C ((x-1)^2)
 | 2 => (X-C 1)^2+C (x^2)
 | 3 => (X-C 1)^2+C ((x-1)^2)

@[simp] theorem f_eval (x z : K) (i : Fin 4) :
    (f x i).eval z =
      (![z^2+x^2,z^2+(x-1)^2,(z-1)^2+x^2,(z-1)^2+(x-1)^2] : Fin 4 → K) i := by
  fin_cases i <;> simp [f]

@[simp] theorem f_aeval {L : Type*} [Field L] [Algebra K L] (x : K) (z : L) (i : Fin 4) :
    aeval z (f x i) = (f (algebraMap K L x) i).eval z := by
  fin_cases i <;> simp [f]

private theorem shifted_separable (s t : K) (ht : t ≠ 0) :
    ((X+C s)^2+C t).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).2
  intro z
  by_contra! h
  have hd : (2 : AlgebraicClosure K)*(z+algebraMap K (AlgebraicClosure K) s)=0 := by
    simpa [derivative_pow,derivative_add,derivative_X,derivative_C] using h.2
  have hz := (mul_eq_zero.mp hd).resolve_left (by norm_num [Polynomial.coeff_one,Polynomial.coeff_X])
  have hn : algebraMap K (AlgebraicClosure K) t ≠ 0 := (_root_.map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr ht
  apply hn
  simpa [hz] using h.1

 theorem f_separable (x : K) (h0 : x ≠ 0) (h1 : x-1 ≠ 0) (i : Fin 4) :
    (f x i).Separable := by
  fin_cases i
  · simpa [f] using shifted_separable (0:K) (x^2) (pow_ne_zero 2 h0)
  · simpa [f] using shifted_separable (0:K) ((x-1)^2) (pow_ne_zero 2 h1)
  · simpa [f,sub_eq_add_neg] using shifted_separable (-1:K) (x^2) (pow_ne_zero 2 h0)
  · simpa [f,sub_eq_add_neg] using shifted_separable (-1:K) ((x-1)^2) (pow_ne_zero 2 h1)

private theorem shifted_monic (s t : K) : ((X+C s)^2+C t).Monic :=
  ((monic_X_add_C s).pow 2).add_of_left (degree_lt_degree (by simp [Polynomial.coeff_one,Polynomial.coeff_X]))
private theorem shifted_degree (s t : K) : ((X+C s)^2+C t).natDegree = 2 := by simp

 theorem f_monic (x : K) (i : Fin 4) : (f x i).Monic := by
  fin_cases i
  · exact monic_X_pow_add_C _ (by decide)
  · exact monic_X_pow_add_C _ (by decide)
  · simpa only [f,sub_eq_add_neg,map_neg] using shifted_monic (-1:K) (x^2)
  · simpa only [f,sub_eq_add_neg,map_neg] using shifted_monic (-1:K) ((x-1)^2)

 theorem f_natDegree (x : K) (i : Fin 4) : (f x i).natDegree = 2 := by
  fin_cases i
  · exact natDegree_X_pow_add_C
  · exact natDegree_X_pow_add_C
  · simpa only [f,sub_eq_add_neg,map_neg] using shifted_degree (-1:K) (x^2)
  · simpa only [f,sub_eq_add_neg,map_neg] using shifted_degree (-1:K) ((x-1)^2)

 theorem f_not_isUnit (x : K) (i : Fin 4) : ¬ IsUnit (f x i) := by
  intro hi
  have he := (f_monic x i).eq_one_of_isUnit hi
  have hh := f_natDegree x i
  rw [he,natDegree_one] at hh
  contradiction

/-- Precisely the elementary resultants that prevent shared finite roots. -/
structure AvoidsExceptional (x : K) : Prop where
  half : 2*x-1 ≠ 0
  zero_side : 4*x^2+1 ≠ 0
  one_side : 4*(x-1)^2+1 ≠ 0
  diagonal : 2*x^2-2*x+1 ≠ 0

 theorem no_common_root (x z : K) (hx : AvoidsExceptional x) :
    Pairwise (fun i j : Fin 4 => ¬ ((f x i).eval z=0 ∧ (f x j).eval z=0)) := by
  have h01 : ¬ ((f x 0).eval z=0 ∧ (f x 1).eval z=0) := by
    rintro ⟨h0,h1⟩; simp [f] at h0 h1
    apply hx.half
    linear_combination h0-h1
  have h02 : ¬ ((f x 0).eval z=0 ∧ (f x 2).eval z=0) := by
    rintro ⟨h0,h2⟩; simp [f] at h0 h2
    apply hx.zero_side
    linear_combination 4*h0-(2*z+1)*(h0-h2)
  have h03 : ¬ ((f x 0).eval z=0 ∧ (f x 3).eval z=0) := by
    rintro ⟨h0,h3⟩; simp [f] at h0 h3
    have hz : z=1-x := by linear_combination (1/2:K)*(h0-h3)
    rw [hz] at h0
    apply hx.diagonal
    linear_combination h0
  have h12 : ¬ ((f x 1).eval z=0 ∧ (f x 2).eval z=0) := by
    rintro ⟨h1,h2⟩; simp [f] at h1 h2
    have hz : z=x := by linear_combination (1/2:K)*(h1-h2)
    rw [hz] at h1
    apply hx.diagonal
    linear_combination h1
  have h13 : ¬ ((f x 1).eval z=0 ∧ (f x 3).eval z=0) := by
    rintro ⟨h1,h3⟩; simp [f] at h1 h3
    apply hx.one_side
    linear_combination 4*h1-(2*z+1)*(h1-h3)
  have h23 : ¬ ((f x 2).eval z=0 ∧ (f x 3).eval z=0) := by
    rintro ⟨h2,h3⟩; simp [f] at h2 h3
    apply hx.half
    linear_combination h2-h3
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01
  · exact h02
  · exact h03
  · exact fun ⟨h1,h0⟩ => h01 ⟨h0,h1⟩
  · exact (hij rfl).elim
  · exact h12
  · exact h13
  · exact fun ⟨h2,h0⟩ => h02 ⟨h0,h2⟩
  · exact fun ⟨h2,h1⟩ => h12 ⟨h1,h2⟩
  · exact (hij rfl).elim
  · exact h23
  · exact fun ⟨h3,h0⟩ => h03 ⟨h0,h3⟩
  · exact fun ⟨h3,h1⟩ => h13 ⟨h1,h3⟩
  · exact fun ⟨h3,h2⟩ => h23 ⟨h2,h3⟩
  · exact (hij rfl).elim

 theorem avoids_map {L : Type*} [Field L] [CharZero L] (φ : K →+* L) (x : K)
    (hx : AvoidsExceptional x) : AvoidsExceptional (φ x) := by
  constructor
  · simpa [map_sub,map_mul,map_add,map_pow,map_ofNat] using (_root_.map_ne_zero φ).mpr hx.half
  · simpa [map_sub,map_mul,map_add,map_pow,map_ofNat] using (_root_.map_ne_zero φ).mpr hx.zero_side
  · simpa [map_sub,map_mul,map_add,map_pow,map_ofNat] using (_root_.map_ne_zero φ).mpr hx.one_side
  · simpa [map_sub,map_mul,map_add,map_pow,map_ofNat] using (_root_.map_ne_zero φ).mpr hx.diagonal

 theorem f_pairwise_coprime (x : K) (hx : AvoidsExceptional x) :
    Pairwise (fun i j : Fin 4 => IsCoprime (f x i) (f x j)) := by
  intro i j hij
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).2
  intro z
  simp only [f_aeval]
  apply not_and_or.mp
  exact no_common_root _ z (avoids_map (algebraMap K (AlgebraicClosure K)) x hx) hij

/-- The first indeterminate avoids every nonzero polynomial exceptional locus. -/
 theorem generic_polynomial_ne_zero (p : K[X]) (hp : p ≠ 0) :
    Polynomial.aeval (RatFunc.X : RatFunc K) p ≠ 0 := by
  simpa [RatFunc.aeval_X_left_eq_algebraMap] using RatFunc.algebraMap_ne_zero hp

private theorem generic_nonzero_of_coeff (p : K[X]) (i : ℕ) (hi : p.coeff i ≠ 0) :
    Polynomial.aeval (RatFunc.X : RatFunc K) p ≠ 0 := by
  apply generic_polynomial_ne_zero
  intro hp; exact hi (hp ▸ coeff_zero i)

 theorem generic_x_ne_zero : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
 theorem generic_x_sub_one_ne_zero : (RatFunc.X : RatFunc K)-1 ≠ 0 := by
  have hh := generic_nonzero_of_coeff (X-1 : K[X]) 1 (by simp [Polynomial.coeff_one,Polynomial.coeff_X])
  simpa only [aeval_sub,aeval_mul,aeval_add,aeval_X,aeval_one,map_pow,aeval_natCast,map_ofNat] using hh

 theorem generic_avoids : AvoidsExceptional (RatFunc.X : RatFunc K) := by
  constructor
  · have hh := generic_nonzero_of_coeff (2*X-1 : K[X]) 1 (by norm_num [Polynomial.coeff_one,Polynomial.coeff_X])
    simpa only [aeval_sub,aeval_mul,aeval_add,aeval_X,aeval_one,map_pow,aeval_natCast,map_ofNat] using hh
  · have hh := generic_nonzero_of_coeff (4*X^2+1 : K[X]) 2 (by norm_num [Polynomial.coeff_one,Polynomial.coeff_X])
    simpa only [aeval_sub,aeval_mul,aeval_add,aeval_X,aeval_one,map_pow,aeval_natCast,map_ofNat] using hh
  · have he : (4*(X-1)^2+1 : K[X]) = 4*X^2-8*X+5 := by ring
    have hh := generic_nonzero_of_coeff (4*(X-1)^2+1 : K[X]) 2 (by rw [he]; norm_num [Polynomial.coeff_one,Polynomial.coeff_X])
    simpa only [aeval_sub,aeval_mul,aeval_add,aeval_X,aeval_one,map_pow,aeval_natCast,map_ofNat] using hh
  · have hh := generic_nonzero_of_coeff (2*X^2-2*X+1 : K[X]) 2 (by norm_num [Polynomial.coeff_one,Polynomial.coeff_X])
    simpa only [aeval_sub,aeval_mul,aeval_add,aeval_X,aeval_one,map_pow,aeval_natCast,map_ofNat] using hh

/-- The actual original four radicands viewed as quadratics in y over K(x). -/
def originalPolynomial (i : Fin 4) : (RatFunc K)[X] := f RatFunc.X i
/-- Their images in the genuine iterated rational function field K(x)(y). -/
def originalValue (i : Fin 4) : RatFunc (RatFunc K) :=
  algebraMap (RatFunc K)[X] (RatFunc (RatFunc K)) (originalPolynomial i)

/-- Every nonempty product is nonsquare: all four ordered original roots are independent.
This is valid over every characteristic-zero coefficient field, hence also over Qbar. -/
 theorem original_products_nonsquare (s : Finset (Fin 4)) (hs : s.Nonempty) :
    ¬ IsSquare (∏ i ∈ s, (originalValue (K:=K) i)) := by
  simp only [originalValue]
  rw [← map_prod]
  apply FourCorner.CoverFields.polynomial_prod_not_isSquare_ratFunc s _ hs
  · intro i hi j hj hij
    exact (f_pairwise_coprime RatFunc.X generic_avoids hij).isRelPrime
  · intro i hi
    exact (f_separable RatFunc.X generic_x_ne_zero generic_x_sub_one_ne_zero i).squarefree
  · intro i hi
    exact f_not_isUnit RatFunc.X i

/-- Multiplication by a nonzero coefficient does not remove the simple polynomial zeros. -/
theorem original_products_scaled_nonsquare (scalar : RatFunc K) (hscalar : scalar ≠ 0)
    (s : Finset (Fin 4)) (hs : s.Nonempty) :
    ¬ IsSquare (algebraMap (RatFunc K) (RatFunc (RatFunc K)) scalar *
      ∏ i ∈ s, originalValue (K:=K) i) := by
  let P := ∏ i ∈ s, originalPolynomial (K:=K) i
  have hu : IsUnit (C scalar : (RatFunc K)[X]) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hscalar)
  have hP : Squarefree P := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (f_pairwise_coprime RatFunc.X generic_avoids hij).isRelPrime
    · intro i hi
      exact (f_separable RatFunc.X generic_x_ne_zero generic_x_sub_one_ne_zero i).squarefree
  have hnP : ¬ IsUnit P := by
    intro hh
    obtain ⟨i,hi⟩ := hs
    exact f_not_isUnit RatFunc.X i (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ hi) hh)
  have hsP : Squarefree ((C scalar)*P) := squarefree_mul_iff.mpr ⟨hu.isRelPrime_left,hu.squarefree,hP⟩
  have hn : ¬ IsUnit ((C scalar)*P) := fun hh => hnP (isUnit_of_mul_isUnit_right hh)
  have hh := FourCorner.CoverFields.squarefree_not_isSquare_fraction
    (F:=RatFunc (RatFunc K)) ((C scalar)*P) hsP hn
  simpa only [map_mul,RatFunc.algebraMap_C,RatFunc.algebraMap_eq_C,P,map_prod,originalValue] using hh

theorem original_negative_products_nonsquare (s : Finset (Fin 4)) (hs : s.Nonempty) :
    ¬ IsSquare (-(∏ i ∈ s, originalValue (K:=K) i)) := by
  simpa using original_products_scaled_nonsquare (-1 : RatFunc K) (by norm_num) s hs

#print axioms original_products_nonsquare
#print axioms generic_avoids
#print axioms f_pairwise_coprime
end FourCorner.OriginalCoverCompletion.OriginalRadicands
