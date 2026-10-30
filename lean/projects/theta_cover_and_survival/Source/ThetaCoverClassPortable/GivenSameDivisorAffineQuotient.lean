import ThetaCoverClassPortable.GivenAffineRelationQuotient
import ThetaCoverClassPortable.SameDivisorRelationInputs
import ThetaCoverClassPortable.Theorems.Thm_CategoryTheory_MorphismProperty_widePullback_base
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FourCorner.ActualAffineQuotient

/-- Actual affineness of the ordered fibre power, including r=0. -/
theorem affine_fibrePow {U S : Scheme} [IsAffine U] [IsAffine S] (f : U ⟶ S) (r : ℕ) :
    IsAffine (fibrePowOver f r) := by
  haveI : IsAffineHom f := inferInstance
  haveI : IsAffineHom (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base (P := @IsAffineHom) (fun _ : Fin r => U)
      (fun _ => f) (fun _ => inferInstance)
  exact isAffine_of_isAffineHom (fibrePowOver.toBase f r)

/-- Exact canonical Spec(C) quotient for the GIVEN R,s,t,hR; no witness is
reselected and no quotient/algebra effectivity premise is inserted. -/
theorem given_sameDivisor_invariant_projection_is_quotient
    {U S : Scheme} [IsAffine U] [IsAffine S]
    (qS : S ⟶ Spec (.of ℚ)) (f : U ⟶ S)
    [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (r : ℕ) (R : Scheme) (s t : R ⟶ fibrePowOver f r)
    (hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r)
    (hclosed : IsClosedImmersion (pullback.lift s t hst))
    (hs : IsFinite s ∧ Flat s ∧ LocallyOfFinitePresentation s ∧ Surjective s ∧
      ∀ x, s.finrank x = r.factorial)
    (ht : IsFinite t ∧ Flat t ∧ LocallyOfFinitePresentation t ∧ Surjective t ∧
      ∀ x, t.finrank x = r.factorial)
    (hR : ∀ ⦃T : Scheme⦄ (u v : T ⟶ fibrePowOver f r)
      (huv : u ≫ fibrePowOver.toBase f r = v ≫ fibrePowOver.toBase f r),
      (∃ w : T ⟶ R, w ≫ s = u ∧ w ≫ t = v) ↔
        SameDivisor f (fun i => u ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
          (fun i => v ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, huv])) :
    letI := affine_fibrePow f r
    letI := hs.1
    letI : IsAffine R := isAffine_of_isAffineHom s
    IsFinite (projection s t) ∧ Flat (projection s t) ∧
      LocallyOfFinitePresentation (projection s t) ∧ Surjective (projection s t) ∧
      IsPullback s t (projection s t) (projection s t) ∧
      Nonempty (IsColimit (Cofork.ofπ (projection s t) (projection_coequalizes s t))) := by
  letI := affine_fibrePow f r
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  haveI : LocallyOfFiniteType (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base (P := @LocallyOfFiniteType) (fun _ : Fin r => U)
      (fun _ => f) (fun _ => inferInstance)
  letI := hs.1
  letI := hs.2.1
  letI := hs.2.2.1
  letI := ht.1
  letI := ht.2.1
  letI := ht.2.2.1
  letI : IsAffine R := isAffine_of_isAffineHom s
  letI := hclosed
  have hm : ∀ {T : Scheme} (a b : T ⟶ R),
      a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b := by
    intro T a b ha hb
    exact FourCorner.AffineRelationRank.relation_joint_mono
      (fibrePowOver.toBase f r) s t hst a b ha hb
  have he := FourCorner.AffineRelationRank.sameDivisor_equivalence f r s t hst hR
  exact given_affine_relation_invariant_projection_is_quotient
    qS (fibrePowOver.toBase f r) s t hst hm he r hs.2.2.2.2

/-- Original caller-shaped given-R quotient interface. ONLY Y=Spec(C) and
its canonical map are packaged; the supplied original R,s,t,hR stay fixed. -/
theorem given_sameDivisor_affine_quotient
    {U S : Scheme} [IsAffine U] [IsAffine S]
    (qS : S ⟶ Spec (.of ℚ)) (f : U ⟶ S)
    [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (r : ℕ) (R : Scheme) (s t : R ⟶ fibrePowOver f r)
    (hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r)
    (hclosed : IsClosedImmersion (pullback.lift s t hst))
    (hs : IsFinite s ∧ Flat s ∧ LocallyOfFinitePresentation s ∧ Surjective s ∧
      ∀ x, s.finrank x = r.factorial)
    (ht : IsFinite t ∧ Flat t ∧ LocallyOfFinitePresentation t ∧ Surjective t ∧
      ∀ x, t.finrank x = r.factorial)
    (hR : ∀ ⦃T : Scheme⦄ (u v : T ⟶ fibrePowOver f r)
      (huv : u ≫ fibrePowOver.toBase f r = v ≫ fibrePowOver.toBase f r),
      (∃ w : T ⟶ R, w ≫ s = u ∧ w ≫ t = v) ↔
        SameDivisor f (fun i => u ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
          (fun i => v ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, huv])) :
    ∃ (Y : Scheme) (_ : IsAffine Y) (p : fibrePowOver f r ⟶ Y)
      (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  letI := affine_fibrePow f r
  letI := hs.1
  letI : IsAffine R := isAffine_of_isAffineHom s
  obtain ⟨hfin, hf, hfp, hsurj, hpb, hc⟩ :=
    given_sameDivisor_invariant_projection_is_quotient qS f r R s t hst hclosed hs ht hR
  exact ⟨Spec (.of (relationRing s t)), inferInstance, projection s t,
    projection_coequalizes s t, hfin, hf, hfp, hsurj, hpb, hc⟩

/-- Explicit universal property for EVERY target Scheme, proved from the
actual quotient of the GIVEN relation, with no coequalizer as an input. -/
theorem given_sameDivisor_desc_existsUnique
    {U S : Scheme} [IsAffine U] [IsAffine S]
    (qS : S ⟶ Spec (.of ℚ)) (f : U ⟶ S)
    [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (r : ℕ) (R : Scheme) (s t : R ⟶ fibrePowOver f r)
    (hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r)
    (hclosed : IsClosedImmersion (pullback.lift s t hst))
    (hs : IsFinite s ∧ Flat s ∧ LocallyOfFinitePresentation s ∧ Surjective s ∧
      ∀ x, s.finrank x = r.factorial)
    (ht : IsFinite t ∧ Flat t ∧ LocallyOfFinitePresentation t ∧ Surjective t ∧
      ∀ x, t.finrank x = r.factorial)
    (hR : ∀ ⦃T : Scheme⦄ (u v : T ⟶ fibrePowOver f r)
      (huv : u ≫ fibrePowOver.toBase f r = v ≫ fibrePowOver.toBase f r),
      (∃ w : T ⟶ R, w ≫ s = u ∧ w ≫ t = v) ↔
        SameDivisor f (fun i => u ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
          (fun i => v ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, huv]))
    (T : Scheme) (a : fibrePowOver f r ⟶ T) (ha : s ≫ a = t ≫ a) :
    letI := affine_fibrePow f r
    ∃! b : Spec (.of (relationRing s t)) ⟶ T, projection s t ≫ b = a := by
  letI := affine_fibrePow f r
  letI := hs.1
  letI : IsAffine R := isAffine_of_isAffineHom s
  obtain ⟨_, _, _, _, _, hc⟩ :=
    given_sameDivisor_invariant_projection_is_quotient qS f r R s t hst hclosed hs ht hR
  exact projection_desc_existsUnique s t hc T a ha

end FourCorner.ActualAffineQuotient
