import FourCorner.NineFlexGroup
import FourCorner.NineFlexAlgebra
import Mathlib.GroupTheory.OrderOfElement

namespace FourCorner

/-- Lemma lem:nine-flex. The point is in mathlib's actual affine group, and
its order-three relation implies the tangent intersection identity inside
the proof. No flex or division-polynomial premise is assumed. -/
theorem nine_flex {A B : ℚ} (hΔ : (splitCurve A B).Δ ≠ 0)
    (P : (splitCurve A B).toAffine.Point) (hP : P ≠ 0) (h3 : 3 • P = 0) :
    ∃ k : ℚ, k ≠ 0 ∧ k ≠ 1 ∧ k ≠ -1 ∧ k ≠ -(1/2) ∧ k ≠ -2 ∧
      B/A = (1+2*k)/((1-k)*(1+k)^3) ∧
      ∃ r : ℚ, r ≠ 0 ∧ A = r^2*(1-k^2) := by
  obtain ⟨hA,hB,hAB⟩ := (splitCurve_discriminant_ne_zero_iff A B).mp hΔ
  obtain ⟨x,y,m,hy,hcurve,hflex⟩ := splitCurve_three_torsion_tangent P hP h3
  exact flex_parameters_of_tangent hA hB hAB hy hcurve hflex

/-- The same theorem with literal additive order equal to three. -/
theorem nine_flex_of_order_three {A B : ℚ} (hΔ : (splitCurve A B).Δ ≠ 0)
    (P : (splitCurve A B).toAffine.Point) (h3 : addOrderOf P = 3) :
    ∃ k : ℚ, k ≠ 0 ∧ k ≠ 1 ∧ k ≠ -1 ∧ k ≠ -(1/2) ∧ k ≠ -2 ∧
      B/A = (1+2*k)/((1-k)*(1+k)^3) ∧
      ∃ r : ℚ, r ≠ 0 ∧ A = r^2*(1-k^2) := by
  apply nine_flex hΔ P
  · intro he
    rw [he] at h3
    simpa using h3
  · simpa only [h3] using addOrderOf_nsmul_eq_zero P

#print axioms nine_flex
#print axioms nine_flex_of_order_three
end FourCorner
