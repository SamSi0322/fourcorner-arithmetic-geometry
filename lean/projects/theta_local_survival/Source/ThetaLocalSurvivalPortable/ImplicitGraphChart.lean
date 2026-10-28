import ThetaLocalSurvivalPortable.PolynomialImplicitNeighborhood
import Mathlib.Topology.IsLocalHomeomorph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
open Filter
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable {B E F : Type*} [TopologicalSpace B] [TopologicalSpace E]
  [TopologicalSpace F] [Zero F]
  (b : B→E) (f : E×F→F) (e : OpenPartialHomeomorph (E×F) (F×E))

abbrev equationGraph := {q : B×F // f (b q.1,q.2)=0}
abbrev equationGraphSource := {q : equationGraph b f // (b q.1.1,q.1.2)∈e.source}
abbrev equationBaseTarget := {z : B // (0,b z)∈e.target}

variable (he : ∀ w, e w=(f w,w.1))

include he in
theorem equationInverse_coordinates (z : equationBaseTarget b e) :
    f (e.symm (0,b z.1))=0 ∧ (e.symm (0,b z.1)).1=b z.1 := by
  have h := e.right_inv z.2
  rw [he] at h
  exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩

def equationGraphChartForward (q : equationGraphSource b f e) : equationBaseTarget b e :=
  ⟨q.1.1.1,by
    have h := e.map_source q.2
    rw [he,q.1.2] at h
    exact h⟩

def equationGraphChartInverse (z : equationBaseTarget b e) : equationGraphSource b f e :=
  ⟨⟨(z.1,(e.symm (0,b z.1)).2),by
    have h := equationInverse_coordinates b f e he z
    have hp : (b z.1,(e.symm (0,b z.1)).2)=e.symm (0,b z.1) :=
      Prod.ext h.2.symm rfl
    change f (b z.1,(e.symm (0,b z.1)).2)=0
    rw [hp]
    exact h.1⟩,by
      have h := equationInverse_coordinates b f e he z
      have hp : (b z.1,(e.symm (0,b z.1)).2)=e.symm (0,b z.1) :=
        Prod.ext h.2.symm rfl
      change (b z.1,(e.symm (0,b z.1)).2)∈e.source
      rw [hp]
      exact e.map_target z.2⟩

/-- Restrict an actual ambient implicit chart to any continuously varying parameter space. -/
def equationGraphChart (hb : Continuous b) : equationGraphSource b f e ≃ₜ equationBaseTarget b e where
  toFun := equationGraphChartForward b f e he
  invFun := equationGraphChartInverse b f e he
  left_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    change (q.1.1.1,(e.symm (0,b q.1.1.1)).2)=q.1.1
    have h := e.left_inv q.2
    rw [he,q.1.2] at h
    have hs : (e.symm (0,b q.1.1.1)).2=q.1.1.2 :=
      congrArg (fun t : E×F => t.2) h
    exact Prod.ext rfl hs
  right_inv := by intro z; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    have hc : Continuous (fun z : equationBaseTarget b e => e.symm (0,b z.1)) :=
      e.continuousOn_symm.comp_continuous
        (continuous_const.prodMk (hb.comp continuous_subtype_val)) (fun z => z.2)
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.prodMk hc.snd

theorem isOpen_equationGraphSource (hb : Continuous b) :
    IsOpen {q : equationGraph b f | (b q.1.1,q.1.2)∈e.source} :=
  e.open_source.preimage ((hb.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val))

theorem isOpen_equationBaseTarget (hb : Continuous b) :
    IsOpen {z : B | (0,b z)∈e.target} :=
  e.open_target.preimage (continuous_const.prodMk hb)

include he in
theorem isOpenEmbedding_equationGraphProjection (hb : Continuous b) :
    Topology.IsOpenEmbedding
      (fun q : equationGraphSource b f e => q.1.1.1) := by
  have h := (isOpen_equationBaseTarget b e hb).isOpenEmbedding_subtypeVal.comp
    (equationGraphChart b f e he hb).isOpenEmbedding
  exact h

end FourCorner.ThetaLocalSurvival.StrongTopology
