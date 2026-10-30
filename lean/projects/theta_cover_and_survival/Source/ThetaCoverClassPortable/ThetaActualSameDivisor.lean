import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_sameDivisorScheme
import ThetaCoverClassPortable.ThetaRationalPicardInput
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels AlgebraicGeometry.RelPicard

/-- Actual same-divisor relation after every commutative Q-algebra basechange.
The two finite-flat maps retain constant rank r!; no etale/permutation splitting
is claimed on colliding-root or nilpotent tests. -/
theorem actual_sameDivisorScheme (B : Type) [CommRing B] [Algebra ℚ B] (r : ℕ) :
    let f := SmoothProperCurve.baseChange ℚ (cToBase ℚ) B
    ∃ (R : Scheme) (s t : R ⟶ fibrePowOver f r)
      (hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r),
      IsClosedImmersion (pullback.lift s t hst) ∧
      (IsFinite s ∧ Flat s ∧ LocallyOfFinitePresentation s ∧ Surjective s ∧
        ∀ x, s.finrank x = r.factorial) ∧
      (IsFinite t ∧ Flat t ∧ LocallyOfFinitePresentation t ∧ Surjective t ∧
        ∀ x, t.finrank x = r.factorial) ∧
      ∀ ⦃T' : Scheme⦄ (u v : T' ⟶ fibrePowOver f r)
        (huv : u ≫ fibrePowOver.toBase f r = v ≫ fibrePowOver.toBase f r),
        (∃ w : T' ⟶ R, w ≫ s = u ∧ w ≫ t = v) ↔
          SameDivisor f (fun i => u ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
            (fun i => v ≫ fibrePowOver.proj f r i)
            (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, huv]) := by
  letI : IsProper (cToBase ℚ) := source_proper
  letI : SmoothOfRelativeDimension 1 (cToBase ℚ) := source_smooth
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  exact RelEffCartierDiv.exists_sameDivisorScheme
    (SmoothProperCurve.baseChange ℚ (cToBase ℚ) B) r

#print axioms actual_sameDivisorScheme
end FourCorner.ThetaRationalPicardInput
