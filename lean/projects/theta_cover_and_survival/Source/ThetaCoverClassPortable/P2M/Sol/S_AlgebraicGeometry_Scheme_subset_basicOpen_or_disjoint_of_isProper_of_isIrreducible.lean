import ThetaCoverClassPortable.ProperIrreducibleBasicOpen
open CategoryTheory AlgebraicGeometry
universe u
namespace P2MW.S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible
theorem solution (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of k)) [IsProper t]
    (Z : Set X) (hZ : IsClosed Z) (hZi : IsIrreducible Z)
    (U : X.Opens) (hZU : Z ⊆ U) (g : Γ(X, U)) :
    Z ⊆ X.basicOpen g ∨ Disjoint Z (X.basicOpen g : Set X) :=
  FourCorner.ProperIrreducibleBasicOpen.dichotomy k t Z hZ hZi U hZU g
end P2MW.S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible
