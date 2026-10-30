import ThetaLocalSurvivalPortable.MonicRootBound
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
open Filter Set
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable {T V : Type*} [TopologicalSpace T] [TopologicalSpace V]

/-- Projection of a closed equation space is closed when its vertical coordinates are
locally confined to actual compact subsets. The algebraic application derives this
compact confinement from actual monic integral equations. -/
theorem closed_projection_of_local_compact_bounds (Q : Set (T×V)) (hQ : IsClosed Q)
    (hbound : ∀ y : T,∃ U∈𝓝 y,∃ C : Set V,IsCompact C ∧
      ∀ q∈Q,q.1∈U → q.2∈C) :
    IsClosedMap (fun q : Q => q.1.1) := by
  intro S hS
  let D : Set (T×V) := Subtype.val '' S
  have hD : IsClosed D := hQ.isClosedEmbedding_subtypeVal.isClosedMap _ hS
  apply isClosed_of_closure_subset
  intro y hy
  obtain ⟨U,hU,C,hC,hb⟩ := hbound y
  obtain ⟨W,hWU,hWo,hyW⟩ := mem_nhds_iff.mp hU
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let F : Set T := Prod.fst '' {q : T×C | (q.1,(q.2 : V))∈D}
  have hF : IsClosed F := isClosedMap_fst_of_compactSpace _
    (hD.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hlocal : W ∩ ((fun q : Q => q.1.1) '' S) ⊆ F := by
    rintro z ⟨hzW,q,hqS,rfl⟩
    exact ⟨(q.1.1,⟨q.1.2,hb q.1 q.2 (hWU hzW)⟩),⟨q,hqS,rfl⟩,rfl⟩
  have hyF : y∈F := by
    by_contra hn
    obtain ⟨z,hz,hzS⟩ := mem_closure_iff.mp hy (W∩Fᶜ) (hWo.inter hF.isOpen_compl) ⟨hyW,hn⟩
    exact hz.2 (hlocal ⟨hz.1,hzS⟩)
  obtain ⟨w,hw,hyw⟩ := hyF
  obtain ⟨q,hq,hqeq⟩ := hw
  exact ⟨q,hq,(congrArg Prod.fst hqeq).trans hyw⟩

end FourCorner.ThetaLocalSurvival.StrongTopology
