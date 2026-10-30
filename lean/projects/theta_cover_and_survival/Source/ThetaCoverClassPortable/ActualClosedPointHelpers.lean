import Mathlib.AlgebraicGeometry.AlgClosed.Basic

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry

theorem exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (t : X ⟶ Spec (.of k)) [LocallyOfFiniteType t] (x : X) (hx : IsClosed {x}) :
    ∃ z : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk t,
      z.left (IsLocalRing.closedPoint k) = x := by
  refine ⟨Over.homMk (pointOfClosedPoint t x hx) (pointOfClosedPoint_comp t x hx),?_⟩
  exact pointOfClosedPoint_apply t x hx _

theorem jacobsonSpace_of_locallyOfFiniteType
    {R : Type u} [CommRing R] [IsJacobsonRing R] {X : Scheme.{u}}
    (t : X ⟶ Spec (.of R)) [LocallyOfFiniteType t] : JacobsonSpace X :=
  LocallyOfFiniteType.jacobsonSpace t

theorem exists_mem_isClosed_singleton_ne_of_isIrreducible
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (Z : Set X) (hZc : IsClosed Z) (_hZi : IsIrreducible Z) (x : X)
    (hxZ : x ∈ Z) (hxc : IsClosed {x}) (hZne : Z ≠ {x}) :
    ∃ x' ∈ Z, IsClosed {x'} ∧ x' ≠ x := by
  haveI := LocallyOfFiniteType.jacobsonSpace t
  have hn : (Z \ {x}).Nonempty := by
    by_contra h
    apply hZne
    apply Set.Subset.antisymm
    · intro y hy
      by_contra hyn
      exact h ⟨y,hy,hyn⟩
    · exact Set.singleton_subset_iff.mpr hxZ
  have hloc : IsLocallyClosed (Z \ {x}) := by
    rw [Set.sdiff_eq_compl_inter]
    exact hxc.isOpen_compl.isLocallyClosed.inter hZc.isLocallyClosed
  obtain ⟨y,hy,hyc⟩ := nonempty_inter_closedPoints hn hloc
  exact ⟨y,hy.1,hyc,Set.notMem_singleton_iff.mp hy.2⟩

#print axioms exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
#print axioms exists_mem_isClosed_singleton_ne_of_isIrreducible
end AlgebraicGeometry
