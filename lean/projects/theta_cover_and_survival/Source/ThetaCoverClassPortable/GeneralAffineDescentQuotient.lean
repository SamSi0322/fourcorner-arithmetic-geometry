import ThetaCoverClassPortable.AffineDescentQuotient
import ThetaCoverClassPortable.DescentActionAlongMono

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FourCorner.GeneralAffineDescentQuotient
open FourCorner.AffineDescentCoaction
universe u

/-- No algebra structure on A is supplied in this interface: it is obtained
from the ACTUAL specified structural map of affine schemes. -/
theorem spec_quotient (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Module.Finite R S] [Algebra.Etale R S] [Module.FaithfullyFlat R S]
    (xA : Spec (.of A) ⟶ Spec (.of S)) (𝒜 : DescentAction (s R S) xA) :
    ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (p : Spec (.of A) ⟶ Y)
      (w : pullback.fst (xA≫s R S) (s R S)≫p=𝒜.act≫p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (pullback.fst (xA≫s R S) (s R S)) 𝒜.act p p ∧
      Nonempty (IsColimit (Cofork.ofπ p w)) := by
  obtain ⟨φ,rfl⟩ := Spec.map_surjective xA
  letI : Algebra S A := φ.hom.toAlgebra
  letI : Algebra R A := (φ.hom.comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' (by ext r;rfl)
  exact AffineDescentQuotient.exists_quotient R S A 𝒜

/-- The constructed affine quotient for an arbitrary actual affine object,
transported through its canonical affine scheme isomorphism. -/
theorem exists_quotient (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.Etale R S] [Module.FaithfullyFlat R S]
    {X : Scheme.{u}} [IsAffine X] (x : X ⟶ Spec (.of S))
    (𝒜 : DescentAction (s R S) x) :
    ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (p : X ⟶ Y)
      (w : pullback.fst (x≫s R S) (s R S)≫p=𝒜.act≫p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (pullback.fst (x≫s R S) (s R S)) 𝒜.act p p ∧
      Nonempty (IsColimit (Cofork.ofπ p w)) := by
  let A : Type u := Γ(X,⊤)
  let η : Spec (.of A) ≅ X := X.isoSpec.symm
  let r := DescentActionAlongMono.relMap (s R S) x η.hom
  let a := r≫𝒜.act≫η.inv
  have ha : a≫η.hom=r≫𝒜.act := by simp [a,Category.assoc]
  let 𝒜A := DescentActionAlongMono.ofMap (s R S) x η.hom 𝒜 a ha
  obtain ⟨Y,hY,pA,wA,hfin,hflat,hlfp,hsurj,hrel,hco⟩ :=
    spec_quotient R S A (η.hom≫x) 𝒜A
  haveI := hfin
  haveI := hflat
  haveI := hlfp
  haveI := hsurj
  haveI : IsIso r := by dsimp [r];infer_instance
  let p := η.inv≫pA
  have hk : IsPullback (pullback.fst (x≫s R S) (s R S)) 𝒜.act p p := by
    refine hrel.of_iso (asIso r) η η (Iso.refl Y) ?_ ?_ ?_ ?_
    · exact (DescentActionAlongMono.relMap_fst (s R S) x η.hom).symm
    · exact ha
    · simp [p,Category.assoc]
    · simp [p,Category.assoc]
  haveI : IsFinite p := by dsimp [p];infer_instance
  haveI : Flat p := by dsimp [p];infer_instance
  haveI : LocallyOfFinitePresentation p := by dsimp [p];infer_instance
  haveI : Surjective p := by dsimp [p];infer_instance
  exact ⟨Y,hY,p,hk.w,inferInstance,inferInstance,inferInstance,inferInstance,hk,
    ⟨(show IsKernelPair p _ _ from hk).toCoequalizer (regularEpiOfEffectiveEpi p)⟩⟩
end FourCorner.GeneralAffineDescentQuotient
