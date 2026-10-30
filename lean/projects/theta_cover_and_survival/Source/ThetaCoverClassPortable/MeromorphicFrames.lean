import ThetaCoverClassPortable.IdealMeromorphicAtlas

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle
namespace FourCorner.MeromorphicFrames
variable {X : Scheme} [IsIntegral X]

/-- Actual local frames, actual open cover and regular transition cocycle,
with native function-field values of the frames. -/
structure Atlas (M : X.Modules) where
  Index : Type
  U : Index → X.Opens
  cover : ⨆i,U i=⊤
  affine : ∀i,IsAffineOpen (U i)
  nonempty : ∀i,Nonempty (U i)
  frame : ∀i,Γ(M,U i)
  isFrame : ∀i,IsFrameOn (frame i) (U i)
  q : Index → X.functionField
  q_ne_zero : ∀i,q i≠0
  cocycle : UnitCocycle U
  transition : ∀i j,M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (frame j)=
    cocycle.u i j • M.presheaf.map (homOfLE inf_le_left).op (frame i)
  transition_field : ∀i j,
    letI := nonempty i
    letI := nonempty j
    letI : Nonempty ((U i ⊓ U j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
    algebraMap Γ(X,U i ⊓ U j) X.functionField (cocycle.u i j)=q j/q i

lemma map_map (M : X.Modules) {U V W : X.Opens} (hVU : V≤U) (hWV : W≤V) (s : Γ(M,U)) :
    M.presheaf.map (homOfLE hWV).op (M.presheaf.map (homOfLE hVU).op s)=
      M.presheaf.map (homOfLE (hWV.trans hVU)).op s := by
  rw [←CategoryTheory.comp_apply,←M.presheaf.map_comp]
  rfl

lemma hom_naturality {M N : X.Modules} (e : M ⟶ N) {U V : X.Opens} (h : V≤U) (s : Γ(M,U)) :
    N.presheaf.map (homOfLE h).op (e.app U s)=e.app V (M.presheaf.map (homOfLE h).op s) := by
  have he := e.mapPresheaf.naturality (homOfLE h).op
  exact (congrFun (congrArg (fun f=>(ConcreteCategory.hom f : Γ(M,U)→Γ(N,V))) he) s).symm

namespace Atlas
variable {M N : X.Modules}

abbrev ofIdeal (I : X.IdealSheafData) (hI : I.IsInvertible) : Atlas I.module where
  Index := X
  U := IdealMeromorphicAtlas.U I hI
  cover := IdealMeromorphicAtlas.cover I hI
  affine := IdealMeromorphicAtlas.affine I hI
  nonempty := inferInstance
  frame := IdealMeromorphicAtlas.frame I hI
  isFrame := IdealMeromorphicAtlas.frame_isFrame I hI
  q := IdealMeromorphicAtlas.q I hI
  q_ne_zero := IdealMeromorphicAtlas.q_ne_zero I hI
  cocycle := IdealMeromorphicAtlas.cc I hI
  transition := IdealMeromorphicAtlas.transition I hI
  transition_field := IdealMeromorphicAtlas.transition_field I hI

abbrev ofGlue {ι : Type} (U : ι→X.Opens) [∀i,Nonempty (U i)] (hU : ⨆i,U i=⊤)
    (hAff : ∀i,IsAffineOpen (U i)) (c : UnitCocycle U) (q : ι→X.functionField)
    (hq : ∀i,q i≠0)
    (hc : ∀i j,
      letI : Nonempty ((U i ⊓ U j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
      algebraMap Γ(X,U i ⊓ U j) X.functionField (c.u i j)=q j/q i) : Atlas (glueOfCocycle c) where
  Index := ι
  U := U
  cover := hU
  affine := hAff
  nonempty := inferInstance
  frame := glueFrame c
  isFrame := isFrameOn_glueFrame c
  q := q
  q_ne_zero := hq
  cocycle := c
  transition := map_glueFrame_eq_smul c
  transition_field := hc

abbrev mapIso (A : Atlas M) (e : M ≅ N) : Atlas N where
  Index := A.Index
  U := A.U
  cover := A.cover
  affine := A.affine
  nonempty := A.nonempty
  frame i := e.hom.app (A.U i) (A.frame i)
  isFrame i := (A.isFrame i).map_iso e
  q := A.q
  q_ne_zero := A.q_ne_zero
  cocycle := A.cocycle
  transition i j := by rw [hom_naturality,A.transition,Scheme.Modules.Hom.app_smul,←hom_naturality]
  transition_field := A.transition_field

end Atlas

section Refine
variable {ι κ : Type} {U : ι→X.Opens} (c : UnitCocycle U)
    (V : κ→X.Opens) (f : κ→ι) (h : ∀i,V i≤U (f i))

def refineCocycle : UnitCocycle V where
  u i j := rO (le_inf (inf_le_left.trans (h i)) (inf_le_right.trans (h j))) (c.u (f i) (f j))
  refl i := by rw [c.refl,map_one]
  cocycle i j l := by
    have hh := c.cocycle_le (f i) (f j) (f l)
      (W:=V i ⊓ V j ⊓ V l)
      (le_inf ((inf_le_left.trans inf_le_left).trans (h i)) ((inf_le_left.trans inf_le_right).trans (h j)))
      (le_inf ((inf_le_left.trans inf_le_right).trans (h j)) (inf_le_right.trans (h l)))
      (le_inf ((inf_le_left.trans inf_le_left).trans (h i)) (inf_le_right.trans (h l)))
    simpa only [rO_rO] using hh

end Refine

namespace Atlas
variable {M : X.Modules} (A : Atlas M)

abbrev refine {κ : Type} (V : κ→X.Opens) (hv : ⨆i,V i=⊤) (haff : ∀i,IsAffineOpen (V i))
    (hne : ∀i,Nonempty (V i)) (f : κ→A.Index) (h : ∀i,V i≤A.U (f i)) : Atlas M where
  Index := κ
  U := V
  cover := hv
  affine := haff
  nonempty := hne
  frame i := M.presheaf.map (homOfLE (h i)).op (A.frame (f i))
  isFrame i := ((A.isFrame (f i)).map (homOfLE (h i))).mono (h i)
  q i := A.q (f i)
  q_ne_zero i := A.q_ne_zero (f i)
  cocycle := refineCocycle A.cocycle V f h
  transition i j := by
    have hh := congrArg (M.presheaf.map (homOfLE (le_inf (inf_le_left.trans (h i)) (inf_le_right.trans (h j)))).op)
      (A.transition (f i) (f j))
    simpa only [Scheme.Modules.map_smul,map_map,refineCocycle] using hh
  transition_field i j := by
    letI := hne i
    letI := hne j
    letI := A.nonempty (f i)
    letI := A.nonempty (f j)
    letI : Nonempty ((V i ⊓ V j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
    letI : Nonempty ((A.U (f i) ⊓ A.U (f j) : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
    change algebraMap Γ(X,V i ⊓ V j) X.functionField
      (rO (le_inf (inf_le_left.trans (h i)) (inf_le_right.trans (h j))) (A.cocycle.u (f i) (f j)))=_
    rw [KummerUnitCocycle.germ_res]
    exact A.transition_field (f i) (f j)

end Atlas
end FourCorner.MeromorphicFrames
