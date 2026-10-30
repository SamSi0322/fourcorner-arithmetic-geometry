import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_DescentAction
import ThetaCoverClassPortable.FiniteEtaleActionQuotient
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem solution
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X' : Scheme.{u}} {x' : X' ⟶ Spec (CommRingCat.of R')}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x')
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    A.Effective := by
  classical
  obtain ⟨Y,p,w,hfin,hflat,hlfp,hsurj,hR,⟨hcolim⟩⟩ :=
    FourCorner.FiniteEtaleActionQuotient.exists_quotient R R' x' A haff
  haveI := hfin
  haveI := hflat
  haveI := hsurj
  haveI : QuasiCompact p := inferInstance
  have hco : pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫ x' ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) =
      A.act ≫ x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [pullback.condition,reassoc_of% A.act_comp]
  obtain ⟨f,hpf⟩ := Cofork.IsColimit.desc' hcolim
    (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) hco
  obtain ⟨e,he,-,hc⟩ := DescentAction.effective_of_isPullback_of_flat_surjective
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))) A p w hR f hpf
  exact ⟨Y,f,e,he,hc⟩
