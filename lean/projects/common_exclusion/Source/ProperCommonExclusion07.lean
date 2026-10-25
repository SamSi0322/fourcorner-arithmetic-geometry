import RationalPlaceSource07
import CurveRationalPlace07
import CommonActualDegree
import geometry.SchemeModelFiniteExtension
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.CommonLiteralField
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- The actual smooth proper integral curve obtained by integral-closure-chart
gluing from the literal four-root function field. -/
def properModel07 (t : ℚ) (ht : 1 < t) : CurveModel ℚ (field ℚ t) := by
  have hf := finrank_field_eq_sixteen ℚ (t := t) (by linarith) (by linarith) (by linarith)
  letI : FiniteDimensional (RatFunc ℚ) (field ℚ t) :=
    Module.finite_of_finrank_pos (by rw [hf]; norm_num)
  letI : IsScalarTower ℚ (RatFunc ℚ) (field ℚ t) := by
    refine ⟨fun q r a => ?_⟩
    rw [RatFunc.smul_eq_C_mul]
    simp only [Algebra.smul_def, map_mul, ← RatFunc.algebraMap_eq_C, eq_ratCast, map_ratCast, mul_assoc]
  exact SchemeModelFiniteExtension.model ℚ (field ℚ t)

/-- Its generic-point stalk field is the literal four-root field. -/
def properModel_functionField07 (t : ℚ) (ht : 1 < t) :
    field ℚ t ≃+* (properModel07 t ht).C.functionField :=
  (properModel07 t ht).ffEquiv

theorem proper_common_exclusion07 {t : ℚ} (ht : 1 < t) {r : ℕ}
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpmod : ∀ i, p i % 8 = 1 ∨ p i % 8 = 7)
    (hDelta_gt : 1 < ∏ i, p i) (hDelta : (∏ i, p i) % 8 = 1) {qD : ℚ}
    (hdisc : t ^ 2 - 1 = ((∏ i, p i : ℕ) : ℚ) * qD ^ 2)
    (hrank : (primeLegendreMatrix p hp).rank = r - 1)
    (htint : ‖(t : ℚ_[37])‖ ≤ 1)
    (htres : padicResidue (t : ℚ_[37]) htint = 14 ∨
      padicResidue (t : ℚ_[37]) htint = -14 ∨
      padicResidue (t : ℚ_[37]) htint = 16 ∨
      padicResidue (t : ℚ_[37]) htint = -16) : ∀ M : CurveModel ℚ (field ℚ t),
      IsEmpty {p : Spec (CommRingCat.of ℚ) ⟶ M.C // p ≫ M.toBase = 𝟙 _} := by
  intro M
  refine ⟨fun point => ?_⟩
  obtain ⟨w,hw⟩ := CurveRationalPlace07.point_gives_rational_place M point.1 point.2
  exact no_rational_place07 ht p hp hinj hpmod hDelta_gt hDelta hdisc hrank htint htres w hw

/-- Paper thm:common-exclusion / thm:common-squareclass, including all points
of the actual constructed smooth proper D_t model. -/
theorem proper_D_no_point07 {t : ℚ} (ht : 1 < t) {r : ℕ}
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpmod : ∀ i, p i % 8 = 1 ∨ p i % 8 = 7)
    (hDelta_gt : 1 < ∏ i, p i) (hDelta : (∏ i, p i) % 8 = 1) {qD : ℚ}
    (hdisc : t ^ 2 - 1 = ((∏ i, p i : ℕ) : ℚ) * qD ^ 2)
    (hrank : (primeLegendreMatrix p hp).rank = r - 1)
    (htint : ‖(t : ℚ_[37])‖ ≤ 1)
    (htres : padicResidue (t : ℚ_[37]) htint = 14 ∨
      padicResidue (t : ℚ_[37]) htint = -14 ∨
      padicResidue (t : ℚ_[37]) htint = 16 ∨
      padicResidue (t : ℚ_[37]) htint = -16) : IsEmpty {point : Spec (CommRingCat.of ℚ) ⟶ (properModel07 t ht).C //
      point ≫ (properModel07 t ht).toBase = 𝟙 _} :=
  proper_common_exclusion07 ht p hp hinj hpmod hDelta_gt hDelta hdisc hrank htint htres
    (properModel07 t ht)

theorem properModel_isProper07 (t : ℚ) (ht : 1 < t) :
    IsProper (properModel07 t ht).toBase := inferInstance
theorem properModel_smooth07 (t : ℚ) (ht : 1 < t) :
    SmoothOfRelativeDimension 1 (properModel07 t ht).toBase := inferInstance
theorem properModel_integral07 (t : ℚ) (ht : 1 < t) :
    IsIntegral (properModel07 t ht).C := inferInstance

#print axioms proper_D_no_point07
#print axioms properModel07
#print axioms properModel_functionField07
#print axioms proper_common_exclusion07
end FourCorner.CommonLiteralField
