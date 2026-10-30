import ThetaCoverClassPortable.AffineDescentCoaction
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.Fpqc

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite
universe u
namespace FourCorner.AffineDescentQuotient
open AffineDescentCoaction
variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  (𝒜 : DescentAction (s R S) (x S A))
abbrev C := FlatAlgebraEqualizer.invariants (coaction R S A 𝒜)

def extensionEquiv [Module.Flat R S] : S ⊗[R] C R S A 𝒜 ≃ₐ[S] A :=
  FlatAlgebraEqualizer.equivalence (coaction R S A 𝒜) (counit R S A 𝒜) (coassoc R S A 𝒜)
def extensionEquivCS [Module.Flat R S] : C R S A 𝒜 ⊗[R] S ≃ₐ[R] A :=
  (Algebra.TensorProduct.comm R (C R S A 𝒜) S).trans
    ((extensionEquiv R S A 𝒜).restrictScalars R)
@[simp] lemma extensionEquivCS_tmul [Module.Flat R S] (c:C R S A 𝒜) (s:S) :
    extensionEquivCS R S A 𝒜 (c ⊗ₜ[R] s)=s • (c:A) := by
  change extensionEquiv R S A 𝒜 ((Algebra.TensorProduct.comm R (C R S A 𝒜) S) (c ⊗ₜ[R] s))=_
  rw [Algebra.TensorProduct.comm_tmul]
  exact FlatAlgebraEqualizer.canonical_tmul _ _ _

abbrev p : Spec (.of A) ⟶ Spec (.of (C R S A 𝒜)) :=
  Spec.map (CommRingCat.ofHom (C R S A 𝒜).val.toRingHom)
abbrev f : Spec (.of (C R S A 𝒜)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (C R S A 𝒜)))
lemma p_f : p R S A 𝒜 ≫ f R S A 𝒜=x S A ≫ s R S := by
  rw [x_comp_s,p,f,←Spec.map_comp]
  congr 1

def e [Module.Flat R S] : pullback (f R S A 𝒜) (s R S) ≅ Spec (.of A) :=
  pullbackSpecIso R (C R S A 𝒜) S ≪≫
    Scheme.Spec.mapIso (extensionEquivCS R S A 𝒜).toRingEquiv.toCommRingCatIso.symm.op

@[reassoc (attr:=simp)] lemma e_inv_fst [Module.Flat R S] :
    (e R S A 𝒜).inv ≫ pullback.fst _ _=p R S A 𝒜 := by
  change Spec.map (CommRingCat.ofHom (extensionEquivCS R S A 𝒜).toRingHom) ≫
    (pullbackSpecIso R (C R S A 𝒜) S).inv ≫ pullback.fst _ _=_
  rw [pullbackSpecIso_inv_fst,←Spec.map_comp]
  congr 1
  ext c
  change extensionEquivCS R S A 𝒜 (c ⊗ₜ[R] (1:S))=(c:A)
  rw [extensionEquivCS_tmul,one_smul]
@[reassoc (attr:=simp)] lemma e_inv_snd [Module.Flat R S] :
    (e R S A 𝒜).inv ≫ pullback.snd _ _=x S A := by
  change Spec.map (CommRingCat.ofHom (extensionEquivCS R S A 𝒜).toRingHom) ≫
    (pullbackSpecIso R (C R S A 𝒜) S).inv ≫ pullback.snd _ _=_
  rw [pullbackSpecIso_inv_snd,←Spec.map_comp]
  congr 1
  ext s
  change extensionEquivCS R S A 𝒜 ((1:C R S A 𝒜) ⊗ₜ[R] s)=algebraMap S A s
  rw [extensionEquivCS_tmul]
  change s • (1:A)=algebraMap S A s
  rw [Algebra.smul_def,mul_one]

theorem cartesian [Module.Flat R S] : IsPullback (p R S A 𝒜) (x S A) (f R S A 𝒜) (s R S) :=
  IsPullback.of_iso_pullback ⟨p_f R S A 𝒜⟩ (e R S A 𝒜).symm
    (e_inv_fst R S A 𝒜) (e_inv_snd R S A 𝒜)

/-- The actual invariant algebra coequalizes the two ACTUAL action legs. -/
theorem coequalizes : pullback.fst (x S A ≫ s R S) (s R S) ≫ p R S A 𝒜=
    𝒜.act ≫ p R S A 𝒜 := by
  apply (cancel_epi (q R S A)).mp
  simp only [←Category.assoc]
  rw [q_fst,←spec_delta,p,←Spec.map_comp,←Spec.map_comp]
  congr 1
  ext c
  change (1:S) ⊗ₜ[R] (c:A)=delta R S A 𝒜 c
  exact ((FlatAlgebraEqualizer.mem_invariants _ _).mp c.property).symm

/-- Every affine action over the specified genuine finite-etale FF base has
an actual finite locally free quotient. The quotient algebra is constructed
as its literal coaction equalizer, never an input or certificate. -/
theorem exists_quotient [Module.Finite R S] [Algebra.Etale R S] [Module.FaithfullyFlat R S] :
    ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (p' : Spec (.of A) ⟶ Y)
      (w : pullback.fst (x S A ≫ s R S) (s R S) ≫ p'=𝒜.act ≫ p'),
      IsFinite p' ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' ∧
      IsPullback (pullback.fst (x S A ≫ s R S) (s R S)) 𝒜.act p' p' ∧
      Nonempty (IsColimit (Cofork.ofπ p' w)) := by
  have hsff : (algebraMap R S).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  haveI : Flat (s R S) := ((flat_and_surjective_SpecMap_iff _).mpr hsff).1
  haveI : Surjective (s R S) := ((flat_and_surjective_SpecMap_iff _).mpr hsff).2
  haveI : IsFinite (s R S) := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : LocallyOfFinitePresentation (s R S) :=
    (HasRingHomProperty.Spec_iff (P:=@LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hc := cartesian R S A 𝒜
  haveI : IsFinite (p R S A 𝒜) := MorphismProperty.of_isPullback (P:=@IsFinite) hc.flip inferInstance
  haveI : Flat (p R S A 𝒜) := MorphismProperty.of_isPullback (P:=@Flat) hc.flip inferInstance
  haveI : LocallyOfFinitePresentation (p R S A 𝒜) :=
    MorphismProperty.of_isPullback (P:=@LocallyOfFinitePresentation) hc.flip inferInstance
  haveI : Surjective (p R S A 𝒜) := MorphismProperty.of_isPullback (P:=@Surjective) hc.flip inferInstance
  have ho : IsPullback (pullback.fst (x S A ≫ s R S) (s R S))
      (𝒜.act ≫ x S A) (p R S A 𝒜 ≫ f R S A 𝒜) (s R S) := by
    rw [𝒜.act_comp,p_f]
    exact IsPullback.of_hasPullback _ _
  have hk := ho.of_bot (coequalizes R S A 𝒜) hc
  exact ⟨Spec (.of (C R S A 𝒜)),inferInstance,p R S A 𝒜,coequalizes R S A 𝒜,
    inferInstance,inferInstance,inferInstance,inferInstance,hk,
    ⟨(show IsKernelPair (p R S A 𝒜) _ _ from hk).toCoequalizer
      (regularEpiOfEffectiveEpi (p R S A 𝒜))⟩⟩
end FourCorner.AffineDescentQuotient
