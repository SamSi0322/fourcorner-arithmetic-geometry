import NineThreeG
import NineThreeFPlus
import NineThreeFMinus
import FourCorner.NineThreeHPlus

namespace FourCorner

/-- The literal F-plus model in equation (nine-factors), with d=(t-1)(t+1). -/
def nineFPlusCurve (t : ℚ) : WeierstrassCurve ℚ :=
  splitCurve (2*((t-1)*(t+1))) (-2*t*((t-1)*(t+1)))

/-- The literal F-minus model in equation (nine-factors). -/
def nineFMinusCurve (t : ℚ) : WeierstrassCurve ℚ :=
  splitCurve (2*((t-1)*(t+1))) (2*t*((t-1)*(t+1)))

/-- The literal H-plus model, with T=t+1. -/
def nineHPlusCurve (t : ℚ) : WeierstrassCurve ℚ :=
  splitCurve (2*(t+1)) ((t+1)^2)

/-- Triviality of the actual rational three-torsion subgroup. -/
def TrivialRationalThreeTorsion (E : WeierstrassCurve ℚ) : Prop :=
  ∀ P : E.toAffine.Point, 3 • P = 0 → P = 0

/-- Exact combined statement of paper lemma lem:nine-three-torsion.
All points belong to the actual rational Weierstrass group. -/
theorem nine_three_torsion {t : ℚ}
    (ht : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1) :
    TrivialRationalThreeTorsion (nineGCurve t) ∧
    (1 < t →
      (IsSquare (t+1) →
        TrivialRationalThreeTorsion (nineHPlusCurve t) ∧
        TrivialRationalThreeTorsion (nineFMinusCurve t)) ∧
      ((∃ u : ℚ, t+1 = 2*u^2) →
        TrivialRationalThreeTorsion (nineFPlusCurve t))) := by
  refine ⟨nineG_no_nonzero_three_torsion ht ht1 htm1, ?_⟩
  intro hpos
  constructor
  · intro hsquare
    constructor
    · exact nine_hplus_three_torsion_eq_zero hpos hsquare
    · obtain ⟨z, hz⟩ := hsquare
      have hz' : t+1 = z^2 := by simpa [pow_two] using hz
      exact NineThree.fminus_three_torsion_eq_zero hpos hz'
  · rintro ⟨u, hu⟩
    exact NineThree.fplus_three_torsion_eq_zero hpos hu

/-- The models in the lemma are nonsingular at every allowed parameter. -/
theorem nine_three_models_nonsingular {t : ℚ}
    (ht : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1) :
    (nineGCurve t).Δ ≠ 0 ∧
    (1 < t → (nineHPlusCurve t).Δ ≠ 0 ∧
      (nineFMinusCurve t).Δ ≠ 0 ∧ (nineFPlusCurve t).Δ ≠ 0) := by
  exact ⟨nineGCurve_discriminant_ne_zero ht ht1 htm1,
    fun hpos => ⟨nine_hplus_discriminant_ne_zero hpos,
      NineThree.fminus_discriminant_ne_zero hpos,
      NineThree.fplus_discriminant_ne_zero hpos⟩⟩

end FourCorner

#print axioms FourCorner.nine_three_torsion
#print axioms FourCorner.nine_three_models_nonsingular
