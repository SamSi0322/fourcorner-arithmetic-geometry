import ThetaCoverClassPortable.geometry.ProjectiveLocalization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
A surjective graded ring map induces a genuine closed immersion of projective
spectra. The proof uses the existing scheme charts and their actual ring maps.
-/

noncomputable section

namespace FourCorner.ProjectiveClosedImmersion

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Surjectivity supplies the irrelevant-ideal condition for the actual Proj map. -/
theorem irrelevant_le_map_of_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  change (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
    Ideal.map f (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  apply (HomogeneousIdeal.toIdeal_irrelevant_le ℬ).2
  intro d hd b hb
  obtain ⟨a, ha, rfl⟩ := ProjectiveLocalization.exists_homogeneous_preimage f hf hb
  exact Ideal.mem_map_of_mem f (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd ha)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The map is a closed immersion over each homogeneous affine chart. -/
theorem restriction_isClosedImmersion (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hfs : Function.Surjective f) {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    IsClosedImmersion ((Proj.map f hf) ∣_ Proj.basicOpen 𝒜 s) := by
  let eA := Proj.basicOpenIsoSpec 𝒜 s hs hd
  let eB := Proj.basicOpenIsoSpec ℬ (f s) (f.2 hs) hd
  let hspec : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map f s))) :=
    IsClosedImmersion.spec_of_surjective _ (ProjectiveLocalization.away_map_surjective f hfs hs)
  have heq : (Proj.map f hf) ∣_ Proj.basicOpen 𝒜 s =
      eB.hom ≫ Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ eA.inv := by
    apply (cancel_epi eB.inv).mp
    simp only [Iso.inv_hom_id_assoc]
    apply (cancel_mono (Proj.basicOpen 𝒜 s).ι).mp
    rw [Category.assoc, morphismRestrict_ι]
    simpa only [eA, eB, Proj.awayι, Category.assoc, Proj.map_preimage_basicOpen] using
      Proj.awayι_comp_map f hf hd s hs
  rw [heq]
  infer_instance

/-- Closed immersion of Proj for a surjective graded map, with its standard
irrelevant-ideal condition stated explicitly. -/
theorem isClosedImmersion_map (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hfs : Function.Surjective f) : IsClosedImmersion (Proj.map f hf) := by
  let I := Σ d : {d : ℕ // 0 < d}, 𝒜 d.1
  let U : I → (Proj 𝒜).Opens := fun i => Proj.basicOpen 𝒜 (i.2 : A)
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) U
  · apply Proj.iSup_basicOpen_eq_top
    apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
    intro d hd a ha
    exact Ideal.subset_span ⟨⟨⟨d, hd⟩, ⟨a, ha⟩⟩, rfl⟩
  · intro i
    exact restriction_isClosedImmersion f hf hfs i.2.property i.1.property

/-- Every surjective graded map defines a closed immersion of projective schemes. -/
theorem isClosedImmersion_map_of_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hfs : Function.Surjective f) :
    IsClosedImmersion (Proj.map f (irrelevant_le_map_of_surjective f hfs)) :=
  isClosedImmersion_map f (irrelevant_le_map_of_surjective f hfs) hfs

end FourCorner.ProjectiveClosedImmersion

#check @FourCorner.ProjectiveClosedImmersion.restriction_isClosedImmersion
#check @FourCorner.ProjectiveClosedImmersion.isClosedImmersion_map
#check @FourCorner.ProjectiveClosedImmersion.isClosedImmersion_map_of_surjective
#print axioms FourCorner.ProjectiveClosedImmersion.irrelevant_le_map_of_surjective
#print axioms FourCorner.ProjectiveClosedImmersion.restriction_isClosedImmersion
#print axioms FourCorner.ProjectiveClosedImmersion.isClosedImmersion_map
#print axioms FourCorner.ProjectiveClosedImmersion.isClosedImmersion_map_of_surjective
