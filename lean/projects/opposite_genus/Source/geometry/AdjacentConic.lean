import geometry.AdjacentConicChart
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
The rational-function parametrization of the literal adjacent conic.
Both coordinates satisfy its equation and generate the full rational function
field, because the parameter is their explicit rational expression.
-/

noncomputable section
namespace FourCorner.AdjacentConic

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

def denominatorPolynomial (c : K) : K[X] := C (c ^ 2) * X ^ 2 + C (c ^ 2 - 1)

theorem denominatorPolynomial_ne_zero (c : K) (hc : c ≠ 0) :
    denominatorPolynomial c ≠ 0 := by
  intro h
  have hz := congrArg (fun p : K[X] => p.coeff 2) h
  have hpow : c ^ 2 = 0 := by
    simpa only [denominatorPolynomial, coeff_add, coeff_C_mul, coeff_X_pow,
      coeff_C, coeff_zero, ite_true, show (2 : ℕ) ≠ 0 by decide, ite_false,
      mul_one, add_zero] using hz
  exact hc ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hpow)

theorem denominator_ne_zero (c : K) (hc : c ≠ 0) :
    Chart.denominator (algebraMap K (RatFunc K) c) RatFunc.X ≠ 0 := by
  have h := RatFunc.algebraMap_ne_zero (denominatorPolynomial_ne_zero c hc)
  simpa [denominatorPolynomial, Chart.denominator, add_sub_assoc] using h

def u (c : K) : RatFunc K := Chart.u (algebraMap K (RatFunc K) c) RatFunc.X
def v (c : K) : RatFunc K := Chart.v (algebraMap K (RatFunc K) c) RatFunc.X

theorem conic_identity (c : K) (hc : c ≠ 0) :
    ((algebraMap K (RatFunc K) c) ^ 2 - 1) * (u c) ^ 2 +
      (algebraMap K (RatFunc K) c) ^ 2 * (v c) ^ 2 -
      (algebraMap K (RatFunc K) c) ^ 2 * ((algebraMap K (RatFunc K) c) ^ 2 - 1) = 0 :=
  Chart.conic_identity _ _ (denominator_ne_zero c hc)

theorem c_sub_u_ne_zero (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    algebraMap K (RatFunc K) c - u c ≠ 0 := by
  apply Chart.c_sub_u_ne_zero _ _
  · exact (map_ne_zero (algebraMap K (RatFunc K))).2 hc
  · simpa only [map_sub, map_pow, map_one] using
      (map_ne_zero (algebraMap K (RatFunc K))).2 hA
  · exact denominator_ne_zero c hc

/-- The inverse coordinate is a rational expression in the literal conic coordinates. -/
theorem inverse (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    v c / (algebraMap K (RatFunc K) c - u c) = RatFunc.X := by
  apply Chart.inverse _ _
  · exact (map_ne_zero (algebraMap K (RatFunc K))).2 hc
  · simpa only [map_sub, map_pow, map_one] using
      (map_ne_zero (algebraMap K (RatFunc K))).2 hA
  · exact denominator_ne_zero c hc

/-- These two coordinates generate all of `K(t)`, rather than a proper subfield. -/
theorem coordinates_generate (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    IntermediateField.adjoin K ({u c, v c} : Set (RatFunc K)) = ⊤ := by
  let E := IntermediateField.adjoin K ({u c, v c} : Set (RatFunc K))
  have hu : u c ∈ E := IntermediateField.subset_adjoin K _ (by simp)
  have hv : v c ∈ E := IntermediateField.subset_adjoin K _ (by simp)
  have ht : (RatFunc.X : RatFunc K) ∈ E := by
    rw [← inverse c hc hA]
    exact E.div_mem hv (E.sub_mem (E.algebraMap_mem c) hu)
  apply top_unique
  rw [← RatFunc.adjoin_X (K := K)]
  exact IntermediateField.adjoin_le_iff.mpr (by simpa using ht)

/-- The rational parameter hypotheses exclude the two degenerate conics. -/
theorem rational_nondegenerate (c : ℚ) (hc : 0 < c) (hne : c ≠ 1) :
    c ≠ 0 ∧ c ^ 2 - 1 ≠ 0 := by
  refine ⟨ne_of_gt hc, ?_⟩
  intro hz
  have : c = 1 := by nlinarith
  exact hne this

#print axioms denominator_ne_zero
#print axioms conic_identity
#print axioms inverse
#print axioms coordinates_generate

end FourCorner.AdjacentConic
