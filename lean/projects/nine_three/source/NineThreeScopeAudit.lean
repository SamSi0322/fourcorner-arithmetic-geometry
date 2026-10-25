import NineThreeTorsion

/-! Independent statement expansion: this audit uses literal cubic roots
and quantifies actual rational points, without the aggregate predicates. -/
namespace NineThreeScopeAudit
open FourCorner

theorem literal_equations (t x y : ℚ) :
    ((nineGCurve t).toAffine.Equation x y ↔
      y^2 = x*(x-((t-1)*(t+1))^2)*(x+(t-1)*(t+1))) ∧
    ((nineHPlusCurve t).toAffine.Equation x y ↔
      y^2 = x*(x-2*(t+1))*(x-(t+1)^2)) ∧
    ((nineFMinusCurve t).toAffine.Equation x y ↔
      y^2 = x*(x-2*((t-1)*(t+1)))*(x-2*t*((t-1)*(t+1)))) ∧
    ((nineFPlusCurve t).toAffine.Equation x y ↔
      y^2 = x*(x-2*((t-1)*(t+1)))*(x+2*t*((t-1)*(t+1)))) := by
  simp [nineGCurve, nineHPlusCurve, nineFMinusCurve, nineFPlusCurve,
    splitCurve_equation_iff, sub_neg_eq_add, neg_mul]

theorem exact_paper_statement (t : ℚ) (ht : t ≠ 0) (ht1 : t ≠ 1)
    (htm1 : t ≠ -1) :
    (∀ P : (splitCurve (((t-1)*(t+1))^2) (-((t-1)*(t+1)))).toAffine.Point,
      3 • P = 0 → P = 0) ∧
    (1 < t →
      ((∃ s : ℚ, t+1 = s^2) →
        (∀ P : (splitCurve (2*(t+1)) ((t+1)^2)).toAffine.Point,
          3 • P = 0 → P = 0) ∧
        (∀ P : (splitCurve (2*((t-1)*(t+1)))
            (2*t*((t-1)*(t+1)))).toAffine.Point,
          3 • P = 0 → P = 0)) ∧
      ((∃ s : ℚ, t+1 = 2*s^2) →
        ∀ P : (splitCurve (2*((t-1)*(t+1)))
            (-2*t*((t-1)*(t+1)))).toAffine.Point,
          3 • P = 0 → P = 0)) := by
  obtain ⟨hG, hmore⟩ := nine_three_torsion ht ht1 htm1
  refine ⟨hG, fun hpos => ?_⟩
  obtain ⟨hHM, hF⟩ := hmore hpos
  refine ⟨?_, hF⟩
  rintro ⟨s, hs⟩
  exact hHM ⟨s, by simpa [pow_two] using hs⟩

#print axioms exact_paper_statement
#print axioms literal_equations
end NineThreeScopeAudit
