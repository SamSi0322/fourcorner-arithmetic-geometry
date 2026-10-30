import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_DescentAction_effective_of_finiteEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry

/-- Scheme effectivity for the actual restricted presheaf and its actual
representation-induced descent action. The finite-set affine-neighbourhood
hypothesis remains explicit; no descended scheme or representation is input. -/
theorem exists_representableBy_of_representableBy_restrict_finiteEtale
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1))
    (hG : ∀ T : Over (Spec (CommRingCat.of R)), Presieve.IsSheafFor G
      (Presieve.singleton ((Over.mapPullbackAdj
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))).counit.app T)))
    {X' : Scheme.{u}} (x' : X' ⟶ Spec (CommRingCat.of R'))
    (hX' : (((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R R')))).op) ⋙ G).RepresentableBy
      (Over.mk x'))
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
      (_ : G.RepresentableBy (Over.mk f))
      (e : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≅ X'),
      e.hom ≫ x' = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap R R'))
  let A : DescentAction s x' := DescentAction.ofRepresentableBy s G x' hX'
  obtain ⟨X, f, e, he, hc⟩ := DescentAction.effective_of_finiteEtale R R' A haff
  have hsff : (algebraMap R R').FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  haveI : Flat s := ((flat_and_surjective_SpecMap_iff _).mpr hsff).1
  haveI : Surjective s := ((flat_and_surjective_SpecMap_iff _).mpr hsff).2
  haveI : IsFinite s := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI (T : Over (Spec (CommRingCat.of R))) : EffectiveEpi (pullback.fst T.hom s) := inferInstance
  have hsheaf : ∀ T : Over (Spec (CommRingCat.of R)),
      Presieve.IsSheafFor G (Presieve.singleton (DescentAction.coverT s T)) := by
    intro T
    rw [← DescentAction.counit_app_eq_coverT s T]
    exact hG T
  have hcompat : DescentAction.eRel s x' f e he ≫ DescentAction.repAct s G x' hX' =
      (DescentAction.canonical s f).act ≫ e.hom := hc
  obtain ⟨rep⟩ := DescentAction.representableBy_of_compatible s G x' hX' f e he hsheaf hcompat
  exact ⟨X, f, rep, e, he⟩

end AlgebraicGeometry
