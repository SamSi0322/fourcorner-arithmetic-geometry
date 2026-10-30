import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
The affine algebra prerequisite for a closed immersion on projective spectra:
a surjective graded ring map induces a surjection on degree-zero localizations
away from a homogeneous element. This does not assert projectivity or supply
a quotient grading; those remain separate constructions.
-/

noncomputable section

namespace FourCorner.ProjectiveLocalization

open HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A surjective graded map lifts a homogeneous element in its own degree. -/
theorem exists_homogeneous_preimage (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) {d : ℕ} {b : B} (hb : b ∈ ℬ d) :
    ∃ a : A, a ∈ 𝒜 d ∧ f a = b := by
  obtain ⟨a, ha⟩ := hf b
  refine ⟨DirectSum.decompose 𝒜 a d, (DirectSum.decompose 𝒜 a d).property, ?_⟩
  rw [f.map_directSumDecompose, ha, DirectSum.decompose_of_mem_same ℬ hb]

/-- Surjectivity on the degree-zero coordinate rings of corresponding Proj charts. -/
theorem away_map_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.2 hs) z
  obtain ⟨a, ha, hab⟩ := exists_homogeneous_preimage f hf hb
  refine ⟨Away.mk 𝒜 hs n a ha, ?_⟩
  rw [Away.map_mk]
  subst b
  rfl

end FourCorner.ProjectiveLocalization

#check @FourCorner.ProjectiveLocalization.exists_homogeneous_preimage
#check @FourCorner.ProjectiveLocalization.away_map_surjective
#print axioms FourCorner.ProjectiveLocalization.exists_homogeneous_preimage
#print axioms FourCorner.ProjectiveLocalization.away_map_surjective
