import ThetaCoverClassPortable.ThetaLiteralBinaryRestrictions

namespace FourCorner.ThetaRestrictionHasTwoRoots
open AlgebraicGeometry AlgebraicCurve
open ThetaDGeometricModel ThetaLiteralBinaryRestrictions BinaryQuarticDoubleRoots
open ThetaGeometricContactPoints
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- The singleton/hyperflex possibility is NOT discarded. Its genuine
native projective zero-locus hypothesis gives a fourth power, hence a broad
square, and the already proved literal no-hyperflex result contradicts it. -/
theorem no_singleton (L : ThetaLine K) (P : P1 K) :
    ¬(∀Q : P1 K,ZeroAt (restriction L) Q → Q=P) := by
  intro honly
  obtain ⟨c,a,b,d,hc,hd,he⟩ := singleton_projective_zero_square (homogeneous L) (nonzero L) P honly
  have hsquare := square_of_polynomial_square L c a b d hc he
  cases L with
  | affine α β =>
    obtain ⟨k,x,y,hx,hy,hk,hxy,_,_,_,_⟩ := affine_contacts α β hsquare
    have hzx : ZeroAt (restriction (.affine α β)) (finitePoint x) := by
      apply (zeroAt_finite_iff (homogeneous _) x).mpr
      rw [eval_restriction]
      simpa [ThetaLine.restrict] using hx
    have hzy : ZeroAt (restriction (.affine α β)) (finitePoint y) := by
      apply (zeroAt_finite_iff (homogeneous _) y).mpr
      rw [eval_restriction]
      simpa [ThetaLine.restrict] using hy
    exact hxy (finitePoint_injective ((honly _ hzx).trans (honly _ hzy).symm))
  | vertical t =>
    obtain ⟨k,x,y,hx,hy,hk,hxy,_,_,_,_⟩ := vertical_contacts t hsquare
    have hzx : ZeroAt (restriction (.vertical t)) (finitePoint x) := by
      apply (zeroAt_finite_iff (homogeneous _) x).mpr
      rw [eval_restriction]
      exact hx
    have hzy : ZeroAt (restriction (.vertical t)) (finitePoint y) := by
      apply (zeroAt_finite_iff (homogeneous _) y).mpr
      rw [eval_restriction]
      exact hy
    exact hxy (finitePoint_injective ((honly _ hzx).trans (honly _ hzy).symm))
  | yzero => exact theta_yzero_not_bitangent ((theta_no_hyperflex .yzero).mp hsquare)

/-- EVERY original line restriction has at least two actual native P1 zeros.
This covers infinity and is independent of any assumed odd-divisor support. -/
theorem two_projective_zeros (L : ThetaLine K) :
    ∃P Q : P1 K,P≠Q ∧ ZeroAt (restriction L) P ∧ ZeroAt (restriction L) Q := by
  have h1 := no_singleton L infinity
  push_neg at h1
  obtain ⟨P,hP,hPne⟩ := h1
  have h2 := no_singleton L P
  push_neg at h2
  obtain ⟨Q,hQ,hQne⟩ := h2
  exact ⟨P,Q,hQne.symm,hP,hQ⟩

#print axioms no_singleton
#print axioms two_projective_zeros
end
end FourCorner.ThetaRestrictionHasTwoRoots
