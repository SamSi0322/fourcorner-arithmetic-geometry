import ThetaCoverClassPortable.InvariantSpecProjection
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FourCorner.ActualAffineQuotient

/-- Actual finite/projective/faithfully-flat inclusion gives the four native
geometric properties of the SAME canonical invariant-Spec projection. -/
theorem projection_geometric_properties {X R : Scheme.{u}} [IsAffine X] (s t : R ⟶ X)
    [Module.Finite (relationRing s t) Γ(X, ⊤)]
    [Module.Projective (relationRing s t) Γ(X, ⊤)]
    [Module.FaithfullyFlat (relationRing s t) Γ(X, ⊤)] :
    IsFinite (projection s t) ∧ Flat (projection s t) ∧
      LocallyOfFinitePresentation (projection s t) ∧ Surjective (projection s t) := by
  let C := relationRing s t
  let ι := inclusion s t
  have hfin : RingHom.Finite ι.hom := RingHom.finite_algebraMap.mpr inferInstance
  have hff : ι.hom.FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  letI : Module.FinitePresentation C Γ(X, ⊤) := Module.finitePresentation_of_projective C Γ(X, ⊤)
  have hfp : RingHom.FinitePresentation ι.hom := RingHom.finitePresentation_algebraMap.mpr inferInstance
  haveI : IsFinite (Spec.map ι) := (IsFinite.SpecMap_iff ι).mpr hfin
  haveI : Flat (Spec.map ι) := ((flat_and_surjective_SpecMap_iff ι).mpr hff).1
  haveI : Surjective (Spec.map ι) := ((flat_and_surjective_SpecMap_iff ι).mpr hff).2
  haveI : LocallyOfFinitePresentation (Spec.map ι) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr hfp
  change IsFinite (X.isoSpec.hom ≫ Spec.map ι) ∧ Flat (X.isoSpec.hom ≫ Spec.map ι) ∧
    LocallyOfFinitePresentation (X.isoSpec.hom ≫ Spec.map ι) ∧ Surjective (X.isoSpec.hom ≫ Spec.map ι)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The algebraic invariant pushout, once genuinely established, becomes the
ACTUAL kernel-pair square by the native Spec functor and actual affine Gamma isos. -/
theorem projection_kernelPair {X R : Scheme.{u}} [IsAffine X] [IsAffine R] (s t : R ⟶ X)
    (hpo : IsPushout (inclusion s t) (inclusion s t) s.appTop t.appTop) :
    IsPullback s t (projection s t) (projection s t) := by
  have hpb : IsPullback (Spec.map s.appTop) (Spec.map t.appTop)
      (Spec.map (inclusion s t)) (Spec.map (inclusion s t)) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  refine hpb.of_iso R.isoSpec.symm X.isoSpec.symm X.isoSpec.symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa [Iso.symm_hom] using (Scheme.isoSpec_inv_naturality s)
  · simpa [Iso.symm_hom] using (Scheme.isoSpec_inv_naturality t)
  · simp [projection]
  · simp [projection]

/-- Genuine coequalizer in Scheme, with ARBITRARY scheme targets. Native
flat-surjective AFFINE regular epimorphism is proved, not a quotient assumption. -/
theorem projection_isColimit {X R : Scheme.{u}} [IsAffine X] [IsAffine R] (s t : R ⟶ X)
    [Module.Finite (relationRing s t) Γ(X, ⊤)]
    [Module.Projective (relationRing s t) Γ(X, ⊤)]
    [Module.FaithfullyFlat (relationRing s t) Γ(X, ⊤)]
    (hpo : IsPushout (inclusion s t) (inclusion s t) s.appTop t.appTop) :
    Nonempty (IsColimit (Cofork.ofπ (projection s t) (projection_coequalizes s t))) := by
  obtain ⟨_, hf, _, hs⟩ := projection_geometric_properties s t
  haveI := hf
  haveI := hs
  haveI : IsRegularEpi (projection s t) :=
    isRegularEpi_of_flat_of_surjective_of_isAffine (projection s t)
  have hk : IsKernelPair (projection s t) s t := projection_kernelPair s t hpo
  exact ⟨hk.toCoequalizer'⟩

/-- Independent Spec/Gamma tail, conditional only on the actual algebra facts;
the later given-relation endpoint discharges ALL these facts internally. -/
theorem projection_is_quotient_of_algebra_data {X R : Scheme.{u}} [IsAffine X] [IsAffine R]
    (s t : R ⟶ X)
    [Module.Finite (relationRing s t) Γ(X, ⊤)]
    [Module.Projective (relationRing s t) Γ(X, ⊤)]
    [Module.FaithfullyFlat (relationRing s t) Γ(X, ⊤)]
    (hpo : IsPushout (inclusion s t) (inclusion s t) s.appTop t.appTop) :
    IsFinite (projection s t) ∧ Flat (projection s t) ∧
      LocallyOfFinitePresentation (projection s t) ∧ Surjective (projection s t) ∧
      IsPullback s t (projection s t) (projection s t) ∧
      Nonempty (IsColimit (Cofork.ofπ (projection s t) (projection_coequalizes s t))) := by
  obtain ⟨hfin, hf, hfp, hs⟩ := projection_geometric_properties s t
  exact ⟨hfin, hf, hfp, hs, projection_kernelPair s t hpo, projection_isColimit s t hpo⟩

/-- Explicit all-Scheme factorization and uniqueness from the ACTUAL coequalizer. -/
theorem projection_desc_existsUnique {X R : Scheme.{u}} [IsAffine X] [IsAffine R]
    (s t : R ⟶ X)
    (hc : Nonempty (IsColimit (Cofork.ofπ (projection s t) (projection_coequalizes s t))))
    (T : Scheme.{u}) (a : X ⟶ T) (ha : s ≫ a = t ≫ a) :
    ∃! b : Spec (.of (relationRing s t)) ⟶ T, projection s t ≫ b = a := by
  let h := hc.some
  have hfac : projection s t ≫ h.desc (Cofork.ofπ a ha) = a := Cofork.IsColimit.π_desc h
  refine ⟨h.desc (Cofork.ofπ a ha), hfac, ?_⟩
  intro b hb
  apply Cofork.IsColimit.hom_ext h
  exact hb.trans hfac.symm

end FourCorner.ActualAffineQuotient
