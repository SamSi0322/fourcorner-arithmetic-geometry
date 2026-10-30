import HasseFinalDyadic
import HasseCorrectedOddProduct

/-! Full thm:hp-uniform by a direct arithmetic alternative to the manuscript's
Brauer/Picard construction. Every local sign is evaluated on the SAME actual
rational tangent coefficient; its finite product is proved from quadratic
reciprocity. All rational parameters, the original Domain, literal Loc and
the complete projective source (including its boundary) are retained. -/
namespace FourCorner.HasseUniformNoPoint

open HasseRationalSource HasseProjectivePoint HasseAnchorChoice
open HasseObstructionArithmetic HasseConstantCorrection HasseFinalDyadic HasseSignAlgebra

/-- Every actual rational homogeneous source point forces the literal
manuscript obstruction bit to vanish. -/
theorem obstruction_zero (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) : T p=0 := by
  let D := tangentData p hp P
  have hglob := correctedSign_parameter_finite_product p hp P D
  rw [HasseCorrectedOddProduct.correctedOdd_product p hp hL P D] at hglob
  have hlocal := correctedDyadic_T_product p hp hL P D
  have hbit : bitSign (T p)=1 := hlocal.symm.trans hglob
  apply bitSign_injective
  simpa only [bitSign_zero] using hbit

/-- Full original manuscript thm:hp-uniform. RationalPoint is the actual
Q×-quotient projective locus of all three literal equations of C_p. -/
theorem hp_uniform (p : ℚ) (hp : 1<p) (_hDomain : HasseNorms.Domain p)
    (hLoc : HasseNorms.Loc p) (hT : T p=1) : IsEmpty (RationalPoint p) := by
  refine ⟨fun Q => ?_⟩
  have hz := obstruction_zero p hp hLoc (toHomogeneousPoint p Q)
  rw [hT] at hz
  exact one_ne_zero hz

/-- Exact literal homogeneous-coordinate exclusion, with no projective
boundary coordinate assumed nonzero in its premises. -/
theorem hp_uniform_literal (p : ℚ) (hp : 1<p) (hDomain : HasseNorms.Domain p)
    (hLoc : HasseNorms.Loc p) (hT : T p=1) :
    ¬ ∃ Z U V W TT : ℚ,
      ¬ (Z=0 ∧ U=0 ∧ V=0 ∧ W=0 ∧ TT=0) ∧ CompleteSource11.Source p Z U V W TT := by
  rintro ⟨Z,U,V,W,TT,hn,hEq⟩
  let P : HomogeneousPoint p := ⟨Z,U,V,W,TT,hn,hEq⟩
  exact (hp_uniform p hp hDomain hLoc hT).false (ofHomogeneousPoint p P)

/-- The equivalent nonzero ordered four-square source has no rational point
on the same original domain. -/
theorem hp_uniform_four_squares (p : ℚ) (hp : 1<p) (hDomain : HasseNorms.Domain p)
    (hLoc : HasseNorms.Loc p) (hT : T p=1) : IsEmpty (HasseNorms.LocalPoint ℚ p) := by
  refine ⟨fun S => ?_⟩
  exact (hp_uniform p hp hDomain hLoc hT).false (ofHomogeneousPoint p (ofLocalPoint p S))

#print axioms obstruction_zero
#print axioms hp_uniform
#print axioms hp_uniform_literal
#print axioms hp_uniform_four_squares

end FourCorner.HasseUniformNoPoint
