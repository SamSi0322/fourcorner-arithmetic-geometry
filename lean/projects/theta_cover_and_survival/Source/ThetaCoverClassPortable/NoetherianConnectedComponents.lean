import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Connected.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set TopologicalSpace
namespace FourCorner.ThetaLocalSurvival.ComponentDescent

/-- Connected components of a genuine Noetherian topological space are
clopen, proved from its finite family of actual irreducible components. -/
theorem noetherian_connectedComponent_isClopen {X : Type} [TopologicalSpace X]
    [NoetherianSpace X] (x : X) : IsClopen (connectedComponent x) := by
  let S : Set (Set X) := {Z | Z∈irreducibleComponents X ∧ Disjoint Z (connectedComponent x)}
  have hS : S.Finite := NoetherianSpace.finite_irreducibleComponents.subset (fun _ h => h.1)
  have hc : IsClosed (⋃₀ S) := by
    rw [Set.sUnion_eq_biUnion]
    exact hS.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)
  have heq : (connectedComponent x)ᶜ=⋃₀ S := by
    ext y
    constructor
    · intro hy
      refine Set.mem_sUnion.mpr ⟨irreducibleComponent y,?_,mem_irreducibleComponent⟩
      refine ⟨irreducibleComponent_mem_irreducibleComponents y,?_⟩
      apply Set.disjoint_left.mpr
      intro z hz hc
      have hsub : irreducibleComponent y⊆connectedComponent z :=
        isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent hz
      have hxz : connectedComponent x=connectedComponent z := connectedComponent_eq hc
      apply hy
      rw [hxz]
      exact hsub mem_irreducibleComponent
    · intro hy
      obtain ⟨Z,hZ,hyZ⟩ := Set.mem_sUnion.mp hy
      intro hyC
      exact Set.disjoint_left.mp hZ.2 hyZ hyC
  refine ⟨isClosed_connectedComponent,?_⟩
  rw [←isClosed_compl_iff,heq]
  exact hc

end FourCorner.ThetaLocalSurvival.ComponentDescent
