import FourCorner.FermatSymmetry
import Mathlib.Tactic

/-! Literal local-chart boundary obstructions. These are valid for every
commutative Q-algebra and every Q-valued evaluation; no affine nonvanishing
hypothesis is imposed on the root. Proper-model coverage is not asserted. -/
namespace FourCorner.CommonBoundaryCharts
variable {R : Type*} [CommRing R] [Algebra ℚ R]

private lemma eval_rat (f : R →ₐ[ℚ] ℚ) (q : ℚ) :
    f (algebraMap ℚ R q) = q := by simp

/-- General specialization obstruction, including nonreduced local charts. -/
theorem no_square_two (f : R →ₐ[ℚ] ℚ) (r : R)
    (h : r ^ 2 = 2) : False := by
  have hh := congrArg f h
  simp only [map_pow, map_ofNat] at hh
  exact rational_sq_ne_two (f r) hh

/-- Negative square obstruction after specialization. -/
theorem no_square_neg_s (t : ℚ) (ht : 1 < t) (f : R →ₐ[ℚ] ℚ) (r : R)
    (h : r ^ 2 = algebraMap ℚ R (-(t-1))) : False := by
  have hh := congrArg f h
  simp only [map_pow, eval_rat] at hh
  nlinarith [sq_nonneg (f r)]

/-- At ell=s the regular M root would specialize to sqrt(2). -/
theorem no_eval_at_s (t : ℚ) (ht : t ≠ 1) (f : R →ₐ[ℚ] ℚ) (ell M : R)
    (h : ell * M^2 = algebraMap ℚ R (t-1) * (algebraMap ℚ R (t+1)-ell))
    (he : f ell = t-1) : False := by
  have hh := congrArg f h
  simp only [map_mul, map_pow, map_sub, eval_rat, he] at hh
  have hne : t-1 ≠ 0 := sub_ne_zero.mpr ht
  apply rational_sq_ne_two (f M)
  apply (mul_left_cancel₀ hne)
  nlinarith [hh]

/-- At ell=T the regular C root would specialize to sqrt(2). -/
theorem no_eval_at_T (t : ℚ) (f : R →ₐ[ℚ] ℚ) (ell C : R)
    (h : C^2 = ell-algebraMap ℚ R (t-1)) (he : f ell = t+1) : False := by
  have hh := congrArg f h
  simp only [map_pow, map_sub, eval_rat, he] at hh
  apply rational_sq_ne_two (f C)
  linarith

/-- At ell=-s the regular P root would specialize to sqrt(2). -/
theorem no_eval_at_neg_s (t : ℚ) (f : R →ₐ[ℚ] ℚ) (ell P : R)
    (h : P^2 = ell+algebraMap ℚ R (t+1)) (he : f ell = -(t-1)) : False := by
  have hh := congrArg f h
  simp only [map_pow, map_add, eval_rat, he] at hh
  apply rational_sq_ne_two (f P)
  linarith

/-- At ell=-T the regular B root would specialize to sqrt(2). -/
theorem no_eval_at_neg_T (t : ℚ) (ht : t ≠ -1) (f : R →ₐ[ℚ] ℚ) (ell B : R)
    (h : ell * B^2 = algebraMap ℚ R (t+1) * (ell+algebraMap ℚ R (t-1)))
    (he : f ell = -(t+1)) : False := by
  have hh := congrArg f h
  simp only [map_mul, map_pow, map_add, eval_rat, he] at hh
  have hne : -(t+1) ≠ 0 := by intro hz; apply ht; linarith
  apply rational_sq_ne_two (f B)
  apply (mul_left_cancel₀ hne)
  nlinarith [hh]

/-- At ell=0 the regular C root has the negative square -(t-1). -/
theorem no_eval_at_zero (t : ℚ) (ht : 1 < t) (f : R →ₐ[ℚ] ℚ) (ell C : R)
    (h : C^2 = ell-algebraMap ℚ R (t-1)) (he : f ell = 0) : False := by
  have hh := congrArg f h
  simp only [map_pow, map_sub, eval_rat, he] at hh
  nlinarith [sq_nonneg (f C)]

/-- Infinity is treated in its actual reciprocal chart z=1/ell. The
regular M root has square (t-1)((t+1)z-1), so z=0 is excluded. -/
theorem no_eval_at_infinity (t : ℚ) (ht : 1 < t) (f : R →ₐ[ℚ] ℚ) (z M : R)
    (h : M^2 = algebraMap ℚ R (t-1) * (algebraMap ℚ R (t+1)*z-1))
    (hz : f z = 0) : False := by
  have hh := congrArg f h
  simp only [map_pow, map_mul, map_sub, map_one, eval_rat, hz] at hh
  nlinarith [sq_nonneg (f M)]

/-- The five finite branch values are literally distinct for the full
paper parameter range, including t<1. Infinity is the sixth value. -/
theorem finite_branch_values_distinct (t : ℚ)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    ([0, t-1, t+1, -(t-1), -(t+1)] : List ℚ).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff,
    not_false_eq_true, List.nodup_nil, not_or, and_true]
  repeat' constructor
  all_goals intro h
  all_goals first
    | exact h0 (by linarith)
    | exact h1 (by linarith)
    | exact hm (by linarith)
    | linarith

#print axioms finite_branch_values_distinct
#print axioms no_eval_at_s
#print axioms no_eval_at_T
#print axioms no_eval_at_neg_s
#print axioms no_eval_at_neg_T
#print axioms no_eval_at_zero
#print axioms no_eval_at_infinity
end FourCorner.CommonBoundaryCharts
