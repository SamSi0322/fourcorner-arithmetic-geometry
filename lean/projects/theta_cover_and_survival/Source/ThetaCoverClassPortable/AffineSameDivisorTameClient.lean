import ThetaCoverClassPortable.AffineRelationTameInputs
import ThetaCoverClassPortable.ThetaActualSameDivisor

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FourCorner.AffineRelationRank

/-- The genuine same-divisor construction on an affine smooth curve produces
actual affine finite-relation tame inputs. All rank/unit/scalar compatibility,
joint monomorphism, test-scheme equivalence and finite-type inputs are discharged. -/
theorem exists_affine_sameDivisor_tame {U S : Scheme} [IsAffine U] [IsAffine S]
    (qS : S ⟶ Spec (.of ℚ)) (f : U ⟶ S)
    [IsSeparated f] [SmoothOfRelativeDimension 1 f] (r : ℕ) :
    ∃ (R : Scheme) (s t : R ⟶ fibrePowOver f r)
      (hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r),
      IsClosedImmersion (pullback.lift s t hst) ∧
      (IsFinite s ∧ Flat s ∧ LocallyOfFinitePresentation s ∧ Surjective s ∧
        ∀ x, s.finrank x = r.factorial) ∧
      (IsFinite t ∧ Flat t ∧ LocallyOfFinitePresentation t ∧ Surjective t ∧
        ∀ x, t.finrank x = r.factorial) ∧
      (∀ {T : Scheme} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b) ∧
      (∀ T : Scheme, Equivalence fun u v : T ⟶ fibrePowOver f r =>
        ∃ w : T ⟶ R, w ≫ s = u ∧ w ≫ t = v) ∧
      TameInputs qS (fibrePowOver.toBase f r) s t hst r := by
  haveI : IsAffineHom f := inferInstance
  haveI : IsAffineHom (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base (P := @IsAffineHom) (fun _ : Fin r => U)
      (fun _ => f) (fun _ => inferInstance)
  haveI : IsAffine (fibrePowOver f r) := isAffine_of_isAffineHom (fibrePowOver.toBase f r)
  haveI : LocallyOfFiniteType (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base (P := @LocallyOfFiniteType) (fun _ : Fin r => U)
      (fun _ => f) (fun _ => inferInstance)
  obtain ⟨R, s, t, hst, hclosed, hs, ht, hformula⟩ :=
    RelEffCartierDiv.exists_sameDivisorScheme f r
  haveI := hclosed
  haveI := hs.1
  haveI := hs.2.1
  haveI := hs.2.2.1
  have hm : ∀ {T : Scheme} (a b : T ⟶ R),
      a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b := by
    intro T a b ha hb
    exact relation_joint_mono (fibrePowOver.toBase f r) s t hst a b ha hb
  have he := sameDivisor_equivalence f r s t hst hformula
  exact ⟨R, s, t, hst, hclosed, hs, ht, hm, he,
    tame_inputs qS (fibrePowOver.toBase f r) s t hst hm he r hs.2.2.2.2⟩

end FourCorner.AffineRelationRank

namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels AlgebraicGeometry.RelPicard FourCorner.AffineRelationRank

/-- Client on every actual affine curve open U of the literal original C_B.
Only B and the actual affine open are supplied: the smooth/separated fibre-power
geometry, native factorial rank, exact C finiteness and rational tame unit are proved. -/
theorem actual_affine_open_sameDivisor_tame (B : Type) [CommRing B] [Algebra ℚ B]
    (U : (pullback (cToBase ℚ) (SmoothProperCurve.specMap ℚ B)).affineOpens) (r : ℕ) :
    let f := U.1.ι ≫ SmoothProperCurve.baseChange ℚ (cToBase ℚ) B
    ∃ (R : Scheme) (s t : R ⟶ fibrePowOver f r)
      (hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r),
      IsClosedImmersion (pullback.lift s t hst) ∧
      (IsFinite s ∧ Flat s ∧ LocallyOfFinitePresentation s ∧ Surjective s ∧
        ∀ x, s.finrank x = r.factorial) ∧
      (IsFinite t ∧ Flat t ∧ LocallyOfFinitePresentation t ∧ Surjective t ∧
        ∀ x, t.finrank x = r.factorial) ∧
      (∀ {T : Scheme} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b) ∧
      (∀ T : Scheme, Equivalence fun u v : T ⟶ fibrePowOver f r =>
        ∃ w : T ⟶ R, w ≫ s = u ∧ w ≫ t = v) ∧
      TameInputs (SmoothProperCurve.specMap ℚ B) (fibrePowOver.toBase f r) s t hst r := by
  letI : IsProper (cToBase ℚ) := source_proper
  letI : SmoothOfRelativeDimension 1 (cToBase ℚ) := source_smooth
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : IsAffine (U.1 : Scheme) := U.2
  haveI : SmoothOfRelativeDimension 1
      (U.1.ι ≫ SmoothProperCurve.baseChange ℚ (cToBase ℚ) B) :=
    smoothOfRelativeDimension_comp (n := 0) (m := 1) U.1.ι
      (SmoothProperCurve.baseChange ℚ (cToBase ℚ) B)
  exact exists_affine_sameDivisor_tame (SmoothProperCurve.specMap ℚ B)
    (U.1.ι ≫ SmoothProperCurve.baseChange ℚ (cToBase ℚ) B) r

end FourCorner.ThetaRationalPicardInput
