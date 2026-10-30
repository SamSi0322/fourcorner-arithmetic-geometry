import ThetaCoverClassPortable.AffineUniversalFromGivenQuotient
import ThetaCoverClassPortable.GivenSameDivisorAffineQuotient
import ThetaCoverClassPortable.AffineSameDivisorTameClient
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FourCorner.ActualAffineUniversalDivisor

/-- Affine relative effective divisors are represented over every affine QQ-base.
The same relation witness and its all-test classification feed both quotient and descent. -/
theorem exists_isUniversal {U S : Scheme} [IsAffine U] [IsAffine S]
    (qS : S ⟶ Spec (.of ℚ)) (f : U ⟶ S)
    [IsSeparated f] [SmoothOfRelativeDimension 1 f] (r : ℕ) :
    ∃ (Y : Scheme) (_ : IsAffine Y) (y : Y ⟶ S)
      (Duniv : RelEffCartierDiv f r y), Duniv.IsUniversal := by
  obtain ⟨R, s, t, hst, hclosed, hs, ht, hR⟩ :=
    RelEffCartierDiv.exists_sameDivisorScheme f r
  obtain ⟨Y, hYaff, p, w, hpfin, hpflat, hplfp, hpsurj, hsq, ⟨hcoeq⟩⟩ :=
    FourCorner.ActualAffineQuotient.given_sameDivisor_affine_quotient
      qS f r R s t hst hclosed hs ht hR
  obtain ⟨y, Duniv, hU⟩ :=
    FourCorner.AffineDivisorUniversal.AlgebraicGeometry.RelEffCartierDiv.ChartAffine.of_given_quotient
      f r s t hst hR p w hsq hcoeq
  exact ⟨Y, hYaff, y, Duniv, hU⟩

end FourCorner.ActualAffineUniversalDivisor

namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels AlgebraicGeometry.RelPicard

/-- Every actual affine open of the literal original C_B has a universal relative
rank-r effective divisor, on all Scheme-valued tests, for arbitrary QQ-algebra B. -/
theorem actual_affine_open_exists_isUniversal (B : Type) [CommRing B] [Algebra ℚ B]
    (U : (pullback (cToBase ℚ) (SmoothProperCurve.specMap ℚ B)).affineOpens) (r : ℕ) :
    let f := U.1.ι ≫ SmoothProperCurve.baseChange ℚ (cToBase ℚ) B
    ∃ (Y : Scheme) (_ : IsAffine Y) (y : Y ⟶ Spec (.of B))
      (Duniv : RelEffCartierDiv f r y), Duniv.IsUniversal := by
  letI : IsProper (cToBase ℚ) := source_proper
  letI : SmoothOfRelativeDimension 1 (cToBase ℚ) := source_smooth
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : IsAffine (U.1 : Scheme) := U.2
  haveI : SmoothOfRelativeDimension 1
      (U.1.ι ≫ SmoothProperCurve.baseChange ℚ (cToBase ℚ) B) :=
    smoothOfRelativeDimension_comp (n := 0) (m := 1) U.1.ι
      (SmoothProperCurve.baseChange ℚ (cToBase ℚ) B)
  exact FourCorner.ActualAffineUniversalDivisor.exists_isUniversal
    (SmoothProperCurve.specMap ℚ B)
    (U.1.ι ≫ SmoothProperCurve.baseChange ℚ (cToBase ℚ) B) r

end FourCorner.ThetaRationalPicardInput
