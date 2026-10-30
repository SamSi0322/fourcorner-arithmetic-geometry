import ThetaCoverClassPortable.Slot03HighPullbackField

noncomputable section
namespace FourCorner.SchemeFieldBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
variable (c : X ⟶ Spec (.of K))

abbrev fieldAlgebra : Algebra K X.functionField := (baseToFunctionField c).toAlgebra

def sectionEmbedding (U : X.Opens) [Nonempty U] :
    letI := fieldAlgebra c
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Γ(X,U) →ₐ[K] X.functionField := by
  letI := fieldAlgebra c
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  haveI : IsScalarTower K Γ(X,U) X.functionField := Slot03High.section_scalarTower c U
  exact IsScalarTower.toAlgHom K Γ(X,U) X.functionField

lemma sectionEmbedding_injective (U : X.Opens) [Nonempty U] :
    letI := fieldAlgebra c
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Function.Injective (sectionEmbedding c U) :=
  X.germToFunctionField_injective U

lemma tensor_sections_domain (L : Type u) [Field L] [Algebra K L]
    (hd : letI := fieldAlgebra c; IsDomain (L ⊗[K] X.functionField))
    (U : X.Opens) [Nonempty U] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    IsDomain (L ⊗[K] Γ(X,U)) := by
  letI := fieldAlgebra c
  letI := hd
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  let f := sectionEmbedding c U
  let g : L ⊗[K] Γ(X,U) →ₐ[K] L ⊗[K] X.functionField :=
    Algebra.TensorProduct.map (AlgHom.id K L) f
  have hg : Function.Injective g := by
    change Function.Injective (f.toLinearMap.lTensor L)
    exact Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap (sectionEmbedding_injective c U)
  exact Function.Injective.isDomain g.toRingHom hg

lemma isIntegral_pullback (V : X.TwoAffineOpenCover)
    [Nonempty V.U0] [Nonempty V.U1] [Nonempty (V.U0 ⊓ V.U1 : X.Opens)]
    (L : Type u) [Field L] [Algebra K L]
    (hd : letI := fieldAlgebra c; IsDomain (L ⊗[K] X.functionField)) :
    IsIntegral (pullback c (Scheme.TwoAffineOpenCover.specMap K L)) := by
  haveI : IsDomain (L ⊗[K] (V.cover c).A0) := tensor_sections_domain c L hd V.U0
  haveI : IsDomain (L ⊗[K] (V.cover c).A1) := tensor_sections_domain c L hd V.U1
  haveI : IsDomain (L ⊗[K] (V.cover c).A01) := tensor_sections_domain c L hd (V.U0 ⊓ V.U1)
  exact (V.isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct c L).1

lemma geometricallyIntegral (V : X.TwoAffineOpenCover)
    [Nonempty V.U0] [Nonempty V.U1] [Nonempty (V.U0 ⊓ V.U1 : X.Opens)]
    (hd : ∀ (L : Type u) [Field L] [Algebra K L],
      letI := fieldAlgebra c; IsDomain (L ⊗[K] X.functionField)) : GeometricallyIntegral c := by
  refine ⟨geometrically_iff_of_commRing.mpr ?_⟩
  intro L _ _ Y fst snd hpb
  haveI := isIntegral_pullback c V L (hd L)
  haveI : Nonempty Y := Nonempty.map hpb.isoPullback.inv.base inferInstance
  exact isIntegral_of_isOpenImmersion hpb.isoPullback.hom

def pullbackFunctionFieldEquiv (V : X.TwoAffineOpenCover)
    [Nonempty V.U0] [Nonempty V.U1] [Nonempty (V.U0 ⊓ V.U1 : X.Opens)]
    (L : Type u) [Field L] [Algebra K L]
    (hd : letI := fieldAlgebra c; IsDomain (L ⊗[K] X.functionField)) :
    letI := fieldAlgebra c
    letI := isIntegral_pullback c V L hd
    let d := pullback.snd c (Scheme.TwoAffineOpenCover.specMap K L)
    letI := (baseToFunctionField d).toAlgebra
    FractionRing (L ⊗[K] X.functionField) ≃ₐ[L]
      (pullback c (Scheme.TwoAffineOpenCover.specMap K L)).functionField := by
  letI := fieldAlgebra c
  letI := hd
  letI := isIntegral_pullback c V L hd
  let Y := pullback c (Scheme.TwoAffineOpenCover.specMap K L)
  let d := pullback.snd c (Scheme.TwoAffineOpenCover.specMap K L)
  let W := V.pullback c L
  letI := (baseToFunctionField d).toAlgebra
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c V.U0
  haveI : IsScalarTower K Γ(X,V.U0) X.functionField := Slot03High.section_scalarTower c V.U0
  haveI : IsFractionRing Γ(X,V.U0) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V.U0 V.isAffineOpen_U0
  haveI : IsDomain (L ⊗[K] Γ(X,V.U0)) := tensor_sections_domain c L hd V.U0
  haveI : IsDomain (L ⊗[K] (V.cover c).A0) := tensor_sections_domain c L hd V.U0
  haveI : IsDomain (L ⊗[K] (V.cover c).A1) := tensor_sections_domain c L hd V.U1
  haveI : IsDomain (L ⊗[K] (V.cover c).A01) := tensor_sections_domain c L hd (V.U0 ⊓ V.U1)
  obtain ⟨_,hn0,_⟩ := V.isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct c L
  haveI : Nonempty W.U0 := hn0
  let e0 := (V.exists_baseChangeIsos_structureSheaf c L).choose
  letI := Scheme.TwoAffineOpenCover.algebraOfHom d W.U0
  haveI : IsFractionRing Γ(Y,W.U0) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y W.U0 W.isAffineOpen_U0
  haveI : IsScalarTower L Γ(Y,W.U0) Y.functionField := Slot03High.section_scalarTower d W.U0
  let e0' : (L ⊗[K] Γ(X,V.U0)) ≃ₐ[L] Γ(Y,W.U0) := e0
  let e : FractionRing (L ⊗[K] Γ(X,V.U0)) ≃ₐ[L] Y.functionField :=
    IsFractionRing.algEquivOfAlgEquiv e0'
  exact (Slot03High.tensorFractionEquiv K Γ(X,V.U0) X.functionField L).symm.trans e

end FourCorner.SchemeFieldBaseChange
#print axioms FourCorner.SchemeFieldBaseChange.geometricallyIntegral
#print axioms FourCorner.SchemeFieldBaseChange.pullbackFunctionFieldEquiv
