import ThetaCoverClassPortable.MeromorphicFrames

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
namespace FourCorner.MeromorphicFrames.Atlas
variable (X : Scheme) [IsIntegral X]
abbrev UnitIndex := {U : X.affineOpens // Nonempty (U:X.Opens)}
abbrev unitOpen (i : UnitIndex X) : X.Opens := i.val
lemma unitOpen_cover : ⨆i,unitOpen X i=⊤ := by
  apply top_unique
  intro x _
  obtain ⟨_,⟨U,hU,rfl⟩,hxU,_⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact Opens.mem_iSup.mpr ⟨⟨⟨U,hU⟩,⟨⟨x,hxU⟩⟩⟩,hxU⟩

abbrev unit : Atlas (𝟙_ X.Modules) where
  Index := UnitIndex X
  U := unitOpen X
  cover := unitOpen_cover X
  affine i := i.val.property
  nonempty i := i.property
  frame i := unitSection (unitOpen X i)
  isFrame i := isFrameOn_unitSection _
  q _ := 1
  q_ne_zero _ := one_ne_zero
  cocycle := UnitCocycle.trivial (unitOpen X)
  transition i j := by rw [map_unitSection,map_unitSection];exact (one_smul _ _).symm
  transition_field i j := by
    letI : Nonempty (unitOpen X i) := i.property
    letI : Nonempty (unitOpen X j) := j.property
    letI : Nonempty ((unitOpen X i ⊓ unitOpen X j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
    change algebraMap Γ(X,unitOpen X i ⊓ unitOpen X j) X.functionField 1=1/1
    rw [map_one,div_self one_ne_zero]

#print axioms unit
end FourCorner.MeromorphicFrames.Atlas
