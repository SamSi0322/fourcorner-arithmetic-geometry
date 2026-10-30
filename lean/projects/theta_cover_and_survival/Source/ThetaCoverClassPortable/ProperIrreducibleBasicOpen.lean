import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section
open CategoryTheory Opposite
open AlgebraicGeometry
universe u
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourCorner.ProperIrreducibleBasicOpen

theorem reduced_vanishing_subscheme {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  letI : ∀ U, IsReduced (I.subschemeCover.openCover.X U) := by
    intro U
    have hr : (I.ideal U).IsRadical := PrimeSpectrum.isRadical_vanishingIdeal _
    letI : _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp hr
    change IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)))
    infer_instance
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

theorem dichotomy (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of k)) [IsProper t]
    (Z : Set X) (hZ : IsClosed Z) (hZi : IsIrreducible Z)
    (U : X.Opens) (hZU : Z ⊆ U) (g : Γ(X, U)) :
    Z ⊆ X.basicOpen g ∨ Disjoint Z (X.basicOpen g : Set X) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZ⟩ : TopologicalSpace.Closeds X)
  let i := I.subschemeι
  have hs : (I.support : Set X) = Z := by simp [I]
  letI : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [hs]
    exact isIrreducible_iff_irreducibleSpace.mp hZi
  letI : IsReduced I.subscheme := reduced_vanishing_subscheme _
  letI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  letI : IsProper (i ≫ t) := inferInstance
  letI := (isField_of_universallyClosed k (i ≫ t)).toField
  have htop : (⊤ : I.subscheme.Opens) ≤ i ⁻¹ᵁ U := by
    intro z _
    exact hZU (hs ▸ z.2)
  let a : Γ(I.subscheme, ⊤) := i.appLE U ⊤ htop g
  have ha : I.subscheme.basicOpen a = i ⁻¹ᵁ X.basicOpen g := by
    simpa [a] using Scheme.basicOpen_appLE i ⊤ U htop g
  rcases eq_or_ne a 0 with hz | hn
  · right
    rw [Set.disjoint_left]
    intro x hx hxg
    have hxI : x ∈ I.support := by
      change x ∈ (I.support : Set X)
      rwa [hs]
    let z : I.subscheme := ⟨x, hxI⟩
    have : z ∈ I.subscheme.basicOpen a := by rw [ha]; exact hxg
    simpa [hz] using this
  · left
    have ht : I.subscheme.basicOpen a = ⊤ :=
      I.subscheme.basicOpen_of_isUnit (isUnit_iff_ne_zero.mpr hn)
    intro x hx
    have hxI : x ∈ I.support := by
      change x ∈ (I.support : Set X)
      rwa [hs]
    let z : I.subscheme := ⟨x, hxI⟩
    have : z ∈ I.subscheme.basicOpen a := by rw [ht]; trivial
    rw [ha] at this
    exact this

end FourCorner.ProperIrreducibleBasicOpen
