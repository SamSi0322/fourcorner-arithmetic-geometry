import ThetaCoverClassPortable.MeromorphicFrames

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
namespace FourCorner.MeromorphicFrames
open SmoothProperClosedPointPlaces
variable {X : Scheme} [IsIntegral X] {M N : X.Modules}

namespace Atlas
variable (A : Atlas M) (B : Atlas N)
abbrev common (p : A.Index × B.Index) : X.Opens := A.U p.1 ⊓ B.U p.2

lemma common_cover : ⨆p,common A B p=⊤ := by
  apply top_unique
  intro x _
  have ha : x∈⨆i,A.U i := by rw [A.cover];trivial
  have hb : x∈⨆j,B.U j := by rw [B.cover];trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp ha
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hb
  exact Opens.mem_iSup.mpr ⟨(i,j),hi,hj⟩

lemma common_nonempty (p : A.Index × B.Index) : Nonempty (common A B p) := by
  letI := A.nonempty p.1
  letI := B.nonempty p.2
  exact KummerUnitCocycle.nonempty_inf _ _

lemma common_affine {k : Type} [Field k] (c : X ⟶ Spec (.of k)) [IsProper c]
    (p : A.Index × B.Index) : IsAffineOpen (common A B p) :=
  isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal c))
    ⊤ (isAffineOpen_top _) (A.U p.1) (by simp) (B.U p.2) (by simp) (A.affine p.1) (B.affine p.2)

abbrev commonLeft {k : Type} [Field k] (c : X ⟶ Spec (.of k)) [IsProper c] : Atlas M :=
  A.refine (common A B) (common_cover A B) (common_affine A B c) (common_nonempty A B)
    Prod.fst (fun _=>inf_le_left)

abbrev commonRight {k : Type} [Field k] (c : X ⟶ Spec (.of k)) [IsProper c] : Atlas N :=
  B.refine (common A B) (common_cover A B) (common_affine A B c) (common_nonempty A B)
    Prod.snd (fun _=>inf_le_right)

lemma glueIso (A : Atlas M) : Nonempty (M ≅ glueOfCocycle A.cocycle) := by
  obtain ⟨e,_⟩ := exists_iso_glueOfCocycle_app_eq_glueFrame A.cover A.cocycle A.frame A.isFrame A.transition
  exact ⟨e⟩

/-- Genuine Cartier-Weil injectivity for arbitrary actual invertible
modules equipped with their true meromorphic local frames. An actual
common affine refinement and regular-unit comparison are constructed. -/
theorem nonempty_iso_of_equal_orders {k : Type} [Field k] (c : X ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (hord : letI := fieldAlgebra c
      ∀(x : closedPoints X) i j,x.val∈A.U i ⊓ B.U j →
        (placeOfClosedPoint c x).ord (A.q i)=(placeOfClosedPoint c x).ord (B.q j)) : Nonempty (M ≅ N) := by
  let AL := commonLeft A B c
  let BR := commonRight A B c
  letI (p : A.Index × B.Index) : Nonempty (common A B p) := common_nonempty A B p
  obtain ⟨e,_⟩ := CartierWeilInjectivity.exists_iso_of_equal_orders c
    (common A B) (common_affine A B c) AL.cocycle BR.cocycle AL.q BR.q AL.q_ne_zero BR.q_ne_zero
    AL.transition_field BR.transition_field (fun x p hx=>hord x p.1 p.2 hx) (common_cover A B)
  exact ⟨(glueIso AL).some ≪≫ e ≪≫ (glueIso BR).some.symm⟩

end Atlas
#print axioms Atlas.nonempty_iso_of_equal_orders
end FourCorner.MeromorphicFrames
