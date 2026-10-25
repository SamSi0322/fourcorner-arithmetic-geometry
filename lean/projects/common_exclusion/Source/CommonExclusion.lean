import CommonPointSource
import CommonPostModelBoundary

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.CommonExclusion

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- Residue-matrix exclusion on every actual rational point of a genuine model
of the specified literal four-root field. The ordered source comes from that
point's own local ring, including the exclusion of infinity and all zero roots. -/
theorem model_no_rational_point {t : ℚ} (ht : 1 < t) {r : ℕ}
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpmod : ∀ i, p i % 8 = 1 ∨ p i % 8 = 7)
    (hDelta_gt : 1 < ∏ i, p i) (hDelta : (∏ i, p i) % 8 = 1) {qD : ℚ}
    (hdisc : t ^ 2 - 1 = ((∏ i, p i : ℕ) : ℚ) * qD ^ 2)
    (hrank : (primeLegendreMatrix p hp).rank = r - 1)
    (htint : ‖(t : ℚ_[37])‖ ≤ 1)
    (htres : padicResidue (t : ℚ_[37]) htint = 14 ∨
      padicResidue (t : ℚ_[37]) htint = -14 ∨
      padicResidue (t : ℚ_[37]) htint = 16 ∨
      padicResidue (t : ℚ_[37]) htint = -16)
    (M : CurveModel ℚ (CommonLiteralField.field ℚ t)) :
    IsEmpty (Spec (.of ℚ) ⟶ M.C) := by
  refine ⟨fun point => ?_⟩
  exact (common_root_exclusion ht p hp hinj hpmod hDelta_gt hDelta hdisc hrank htint htres).false
    (CommonPointSource.source t ht M point)

/-- Paper thm:common-exclusion, thm:common-squareclass, and
eq:common-excluded-t on the same native normalized complete D_t Scheme that
has the finite literal ell morphism and geometric genus-nine computation.
The parameter squareclass hypothesis is its nonzero rational-square witness. -/
theorem common_exclusion {t : ℚ} (ht : 1 < t) {r : ℕ}
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpmod : ∀ i, p i % 8 = 1 ∨ p i % 8 = 7)
    (hDelta_gt : 1 < ∏ i, p i) (hDelta : (∏ i, p i) % 8 = 1)
    (hdisc : ∃ qD : ℚ, qD ≠ 0 ∧ t ^ 2 - 1 = ((∏ i, p i : ℕ) : ℚ) * qD ^ 2)
    (hrank : (primeLegendreMatrix p hp).rank = r - 1)
    (htint : ‖(t : ℚ_[37])‖ ≤ 1)
    (htres : padicResidue (t : ℚ_[37]) htint = 14 ∨
      padicResidue (t : ℚ_[37]) htint = -14 ∨
      padicResidue (t : ℚ_[37]) htint = 16 ∨
      padicResidue (t : ℚ_[37]) htint = -16) :
    IsEmpty (Spec (.of ℚ) ⟶ CommonPostFiniteP1.commonCurve t
      (by linarith) (by linarith) (by linarith)) := by
  obtain ⟨qD,hqD,hd⟩ := hdisc
  refine ⟨fun point => ?_⟩
  exact (common_root_exclusion ht p hp hinj hpmod hDelta_gt hDelta hd hrank htint htres).false
    (CommonPointSource.sourceForAlgebra t ht (CommonPostGeometricGenus.modelFieldAlgebra t)
      (CommonSchemeModel.model t (by linarith) (by linarith) (by linarith)) point)

end FourCorner.CommonExclusion
#print axioms FourCorner.CommonExclusion.model_no_rational_point
#print axioms FourCorner.CommonExclusion.common_exclusion
