import ThetaCoverClassPortable.FiniteEtaleAffineSchemeCovering

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable {E X A B : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace A] [TopologicalSpace B]

/-- Covering maps transport through genuine open source and target charts whose source
range is the FULL inverse image of the target range. -/
theorem covering_on_open_charts (f : E→X) (j : A→E) (k : B→X) (q : A→B)
    (hf : Continuous f) (hj : Topology.IsOpenEmbedding j) (hk : Topology.IsOpenEmbedding k)
    (hq : IsCoveringMap q) (hcomm : ∀ a,f (j a)=k (q a))
    (hrange : Set.range j=f ⁻¹' Set.range k) :
    IsCoveringMapOn f (Set.range k) := by
  let sH : A ≃ₜ (f ⁻¹' Set.range k) :=
    hj.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let tH : B ≃ₜ Set.range k := hk.isEmbedding.toHomeomorph
  have h := (hq.comp_homeomorph sH.symm).homeomorph_comp tH
  have he : (tH ∘ q ∘ sH.symm)=(Set.range k).restrictPreimage f := by
    funext x
    apply Subtype.ext
    change k (q (sH.symm x))=f x.1
    rw [←hcomm]
    have hs : j (sH.symm x)=x.1 := congrArg Subtype.val (sH.apply_symm_apply x)
    exact congrArg f hs
  rw [he] at h
  exact IsCoveringMapOn.of_isCoveringMap_restrictPreimage (Set.range k) hk.isOpen_range
    (hk.isOpen_range.preimage hf) h

end FourCorner.ThetaLocalSurvival.StrongTopology
