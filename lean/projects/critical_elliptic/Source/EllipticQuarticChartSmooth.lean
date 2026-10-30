import EllipticQuarticModel
import FiniteJacobianSmooth

/-! Native smoothness of the actual dehomogenized quotient rings on the
independent quartic model of y² = x³ - x. No characteristic-zero hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open Algebra AlgebraicGeometry MvPolynomial
universe u
namespace FourCorner.EllipticQuarticChartSmooth
variable (k : Type u) [Field k]

abbrev ring (j : Fin 4) :=
  CriticalQuotientChart.affineRing (EllipticQuarticModel.equation k) j
abbrev equations (j : Fin 4) :=
  CriticalQuotientChart.affineEquation (EllipticQuarticModel.equation k) j
abbrev ideal (j : Fin 4) :=
  CriticalQuotientChart.affineIdeal (EllipticQuarticModel.equation k) j

def columns : Fin 3 → Fin 2 → Fin 3
  | 0 => ![0,1]
  | 1 => ![0,2]
  | 2 => ![1,2]
lemma columns_injective (i : Fin 3) : Function.Injective (columns i) := by
  fin_cases i <;> decide

def pres (j : Fin 4) (i : Fin 3) :
    PreSubmersivePresentation k (ring k j) (Fin 3) (Fin 2) :=
  .naive (v := equations k j) (columns i) (columns_injective i)
def coordinate (j : Fin 4) (a : Fin 3) : ring k j :=
  Ideal.Quotient.mk (ideal k j) (X a)

lemma pres_jacobi (j : Fin 4) (i : Fin 3) :
    (pres k j i).jacobiMatrix = fun a b =>
      pderiv (columns i a) (equations k j b) := by
  apply Matrix.ext
  intro a b
  exact PreSubmersivePresentation.jacobiMatrix_apply (pres k j i) a b
lemma pres_map (j : Fin 4) (i : Fin 3) (p : MvPolynomial (Fin 3) k) :
    algebraMap (pres k j i).Ring (ring k j) p = Ideal.Quotient.mk (ideal k j) p := rfl

lemma equation_zero_zero : equations k 0 0 = X 1 - X 0 ^ 2 := by
  simp [equations, CriticalQuotientChart.affineEquation, CriticalAmbientChart.dehom,
    EllipticQuarticModel.equation, EllipticQuarticModel.conic, CriticalAmbientChart.drop]
lemma equation_zero_one : equations k 0 1 = X 2 ^ 2 - X 0 * X 1 + X 0 := by
  simp [equations, CriticalQuotientChart.affineEquation, CriticalAmbientChart.dehom,
    EllipticQuarticModel.equation, EllipticQuarticModel.cubicClosure, CriticalAmbientChart.drop]
lemma equation_two_zero : equations k 2 0 = X 0 - X 1 ^ 2 := by
  simp [equations, CriticalQuotientChart.affineEquation, CriticalAmbientChart.dehom,
    EllipticQuarticModel.equation, EllipticQuarticModel.conic, CriticalAmbientChart.drop]
lemma equation_two_one : equations k 2 1 = X 2 ^ 2 - X 1 + X 0 * X 1 := by
  simp [equations, CriticalQuotientChart.affineEquation, CriticalAmbientChart.dehom,
    EllipticQuarticModel.equation, EllipticQuarticModel.cubicClosure, CriticalAmbientChart.drop]

/-- All three genuine presentation minors on the V0 chart. -/
theorem jacobian_zero (i : Fin 3) : (pres k 0 i).jacobian =
    ![2 * coordinate k 0 0 ^ 2 + coordinate k 0 1 - 1,
      -4 * coordinate k 0 0 * coordinate k 0 2,
      2 * coordinate k 0 2] i := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, pres_map,
    pres_jacobi, Matrix.det_fin_two]
  fin_cases i
  all_goals simp [columns, equation_zero_zero, equation_zero_one, coordinate, map_ofNat]
  all_goals ring

/-- All three genuine presentation minors on the V2 chart. -/
theorem jacobian_two (i : Fin 3) : (pres k 2 i).jacobian =
    ![2 * coordinate k 2 1 ^ 2 + coordinate k 2 0 - 1,
      2 * coordinate k 2 2,
      -4 * coordinate k 2 1 * coordinate k 2 2] i := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, pres_map,
    pres_jacobi, Matrix.det_fin_two]
  fin_cases i
  all_goals simp [columns, equation_two_zero, equation_two_one, coordinate, map_ofNat]
  all_goals ring

lemma relations_zero (F : Type u) [Field F] [Algebra k F]
    (f : ring k 0 →ₐ[k] F) :
    f (coordinate k 0 1) = f (coordinate k 0 0) ^ 2 ∧
      f (coordinate k 0 2) ^ 2 =
        f (coordinate k 0 0) * f (coordinate k 0 1) - f (coordinate k 0 0) := by
  have hrel (i : Fin 2) : f (Ideal.Quotient.mk (ideal k 0) (equations k 0 i)) = 0 := by
    have h : Ideal.Quotient.mk (ideal k 0) (equations k 0 i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    exact (congrArg f h).trans (map_zero f)
  have h0 := hrel 0
  have h1 := hrel 1
  rw [equation_zero_zero] at h0
  rw [equation_zero_one] at h1
  simp only [map_sub, map_pow, map_mul, map_add] at h0 h1
  constructor <;> dsimp [coordinate]
  · linear_combination h0
  · linear_combination h1

lemma relations_two (F : Type u) [Field F] [Algebra k F]
    (f : ring k 2 →ₐ[k] F) :
    f (coordinate k 2 0) = f (coordinate k 2 1) ^ 2 ∧
      f (coordinate k 2 2) ^ 2 =
        f (coordinate k 2 1) - f (coordinate k 2 0) * f (coordinate k 2 1) := by
  have hrel (i : Fin 2) : f (Ideal.Quotient.mk (ideal k 2) (equations k 2 i)) = 0 := by
    have h : Ideal.Quotient.mk (ideal k 2) (equations k 2 i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    exact (congrArg f h).trans (map_zero f)
  have h0 := hrel 0
  have h1 := hrel 1
  rw [equation_two_zero] at h0
  rw [equation_two_one] at h1
  simp only [map_sub, map_pow, map_mul, map_add] at h0 h1
  constructor <;> dsimp [coordinate]
  · linear_combination h0
  · linear_combination h1

lemma cubic_derivative_nonzero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {a : F} (ha : a ^ 3 - a = 0) : 3 * a ^ 2 - 1 ≠ 0 := by
  intro h
  have hm : (2 : F) * a = 0 := by linear_combination a * h - 3 * ha
  have hz : a = 0 := (mul_eq_zero.mp hm).resolve_left h2
  simpa [hz] using h

theorem field_point_jacobian_zero (h2 : (2 : k) ≠ 0)
    (F : Type u) [Field F] [Algebra k F] (f : ring k 0 →ₐ[k] F) :
    ∃ i : Fin 3, f (pres k 0 i).jacobian ≠ 0 := by
  have h2F : (2 : F) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k F)).mpr h2
  obtain ⟨h0,h1⟩ := relations_zero k F f
  by_cases hc : f (coordinate k 0 2) = 0
  · refine ⟨0, ?_⟩
    rw [jacobian_zero]
    simp only [Matrix.cons_val_zero, map_sub, map_add, map_mul, map_ofNat, map_pow, map_one]
    rw [h0]
    have ha : f (coordinate k 0 0) ^ 3 - f (coordinate k 0 0) = 0 := by
      rw [h0, hc] at h1
      linear_combination -h1
    convert cubic_derivative_nonzero h2F ha using 1 <;> ring
  · refine ⟨2, ?_⟩
    rw [jacobian_zero]
    change f (2 * coordinate k 0 2) ≠ 0
    rw [map_mul, map_ofNat]
    exact mul_ne_zero h2F hc

theorem field_point_jacobian_two (h2 : (2 : k) ≠ 0)
    (F : Type u) [Field F] [Algebra k F] (f : ring k 2 →ₐ[k] F) :
    ∃ i : Fin 3, f (pres k 2 i).jacobian ≠ 0 := by
  have h2F : (2 : F) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k F)).mpr h2
  obtain ⟨h0,h1⟩ := relations_two k F f
  by_cases hc : f (coordinate k 2 2) = 0
  · refine ⟨0, ?_⟩
    rw [jacobian_two]
    simp only [Matrix.cons_val_zero, map_sub, map_add, map_mul, map_ofNat, map_pow, map_one]
    rw [h0]
    have ha : f (coordinate k 2 1) ^ 3 - f (coordinate k 2 1) = 0 := by
      rw [h0, hc] at h1
      linear_combination h1
    convert cubic_derivative_nonzero h2F ha using 1 <;> ring
  · refine ⟨1, ?_⟩
    rw [jacobian_two]
    change f (2 * coordinate k 2 2) ≠ 0
    rw [map_mul, map_ofNat]
    exact mul_ne_zero h2F hc

/-- Actual native affine-scheme smoothness on the V0 chart. -/
theorem affine_zero_smooth (h2 : (2 : k) ≠ 0) : SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap k (ring k 0)))) := by
  have hs := FiniteJacobianSmooth.jacobian_span_of_field_points (pres k 0)
    (field_point_jacobian_zero k h2)
  have h := FiniteJacobianSmooth.spec_smooth_of_jacobian_span (pres k 0) hs
  simpa using h

/-- Actual native affine-scheme smoothness on the V2 chart. -/
theorem affine_two_smooth (h2 : (2 : k) ≠ 0) : SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap k (ring k 2)))) := by
  have hs := FiniteJacobianSmooth.jacobian_span_of_field_points (pres k 2)
    (field_point_jacobian_two k h2)
  have h := FiniteJacobianSmooth.spec_smooth_of_jacobian_span (pres k 2) hs
  simpa using h

end FourCorner.EllipticQuarticChartSmooth
#print axioms FourCorner.EllipticQuarticChartSmooth.jacobian_zero
#print axioms FourCorner.EllipticQuarticChartSmooth.jacobian_two
#print axioms FourCorner.EllipticQuarticChartSmooth.field_point_jacobian_zero
#print axioms FourCorner.EllipticQuarticChartSmooth.field_point_jacobian_two
#print axioms FourCorner.EllipticQuarticChartSmooth.affine_zero_smooth
#print axioms FourCorner.EllipticQuarticChartSmooth.affine_two_smooth
