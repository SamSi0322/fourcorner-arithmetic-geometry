import ThetaCoverClassPortable.ActualSplitQuadratic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace FourCorner.ThetaQuadraticContactBaseChange
open ThetaQuadraticCurve ThetaQuadraticContactAlgebra ThetaQuadraticGeometricContacts
local instance : Algebra F K := coefficientEmbedding.toRingHom.toAlgebra

def pairTensor : (K ⊗[F] contactField) →ₐ[K] K×K :=
  { (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom F K (K×K))
      ((embedding true).prod (embedding false)) (fun _ _ => Commute.all _ _)).toRingHom with
    commutes' := by intro k;simp [Algebra.TensorProduct.algebraMap_apply,Algebra.TensorProduct.lift_tmul] }

theorem pairTensor_tmul (k : K) (z : contactField) :
    pairTensor (k ⊗ₜ[F] z)=(k*embedding true z,k*embedding false z) := by
  simp [pairTensor,Algebra.TensorProduct.lift_tmul]

theorem pairTensor_surjective : Function.Surjective pairTensor := by
  rintro ⟨u,v⟩
  refine ⟨((u+v)/2) ⊗ₜ[F] (1:contactField)+((u-v)/(2*root)) ⊗ₜ[F] ordinate,?_⟩
  rw [map_add,pairTensor_tmul,pairTensor_tmul]
  simp only [map_one,embedding_ordinate,rootValue,Bool.false_eq_true,if_true,if_false]
  apply Prod.ext <;> dsimp
  · field_simp [root_ne_zero]
    ring
  · field_simp [root_ne_zero]
    ring

/-- Exact scalar extension of the actual closed quadratic contact algebra. -/
def tensorEquiv : (K ⊗[F] contactField) ≃ₐ[K] K×K := by
  have hd : Module.finrank K (K ⊗[F] contactField)=Module.finrank K (K×K) := by
    rw [Module.finrank_eq_card_basis ((QuadraticAlgebra.basis (2/99:F) 0).baseChange K)]
    simp
  exact AlgEquiv.ofBijective pairTensor
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=pairTensor.toLinearMap) hd).mpr
      pairTensor_surjective,pairTensor_surjective⟩

theorem tensorEquiv_one : tensorEquiv (1 ⊗ₜ[F] (1:contactField))=(1,1) := by
  change tensorEquiv 1=1
  exact map_one tensorEquiv

theorem tensorEquiv_ordinate : tensorEquiv (1 ⊗ₜ[F] ordinate)=(root,-root) := by
  change pairTensor (1 ⊗ₜ[F] ordinate)=_
  simp only [pairTensor_tmul,embedding_ordinate,rootValue,Bool.false_eq_true,if_true,if_false,one_mul]

def embeddingsPair : contactField →ₐ[F] K×K := (embedding true).prod (embedding false)

theorem tensorEquiv_includeRight :
    tensorEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : contactField →ₐ[F] K ⊗[F] contactField).toRingHom=
        embeddingsPair.toRingHom := by
  let phi : contactField →ₐ[F] K×K :=
    (tensorEquiv.toAlgHom.restrictScalars F).comp Algebra.TensorProduct.includeRight
  have he : phi=embeddingsPair := by
    apply QuadraticAlgebra.algHom_ext
    change tensorEquiv (1 ⊗ₜ[F] ordinate)=(embedding true ordinate,embedding false ordinate)
    rw [tensorEquiv_ordinate,embedding_ordinate,embedding_ordinate]
    rfl
  exact congrArg AlgHom.toRingHom he

abbrev basechangedContact := pullback extensionMap pointToBase

/-- The actual categorical contact-scheme base change splits into the
actual product algebra. This is effective base change, not fixed labels. -/
def splitSchemeIso : basechangedContact ≅ Spec (.of (K×K)) :=
  (pullbackSpecIso F K contactField) ≪≫
    Scheme.Spec.mapIso tensorEquiv.toRingEquiv.toCommRingCatIso.symm.op

@[reassoc] theorem tensorIso_inv_fst :
    (pullbackSpecIso F K contactField).inv ≫ pullback.fst extensionMap pointToBase=
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[F] contactField))) :=
  pullbackSpecIso_inv_fst F K contactField

@[reassoc] theorem tensorIso_inv_snd :
    (pullbackSpecIso F K contactField).inv ≫ pullback.snd extensionMap pointToBase=
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : contactField →ₐ[F] K ⊗[F] contactField).toRingHom) :=
  pullbackSpecIso_inv_snd F K contactField

@[reassoc (attr := simp)] theorem splitSchemeIso_inv_fst :
    splitSchemeIso.inv ≫ pullback.fst extensionMap pointToBase=
      Spec.map (CommRingCat.ofHom (algebraMap K (K×K))) := by
  simp only [splitSchemeIso,Iso.trans_inv,Category.assoc,tensorIso_inv_fst]
  change Spec.map (CommRingCat.ofHom tensorEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[F] contactField)))=_
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext tensorEquiv.commutes

@[reassoc (attr := simp)] theorem splitSchemeIso_inv_snd :
    splitSchemeIso.inv ≫ pullback.snd extensionMap pointToBase=
      Spec.map (CommRingCat.ofHom embeddingsPair.toRingHom) := by
  simp only [splitSchemeIso,Iso.trans_inv,Category.assoc,tensorIso_inv_snd]
  change Spec.map (CommRingCat.ofHom tensorEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : contactField →ₐ[F] K ⊗[F] contactField).toRingHom)=_
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact tensorEquiv_includeRight

end FourCorner.ThetaQuadraticContactBaseChange
