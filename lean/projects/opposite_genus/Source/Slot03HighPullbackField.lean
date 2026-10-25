import Slot03HighTensorFraction

noncomputable section
namespace FourCorner.Slot03High
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct
universe u

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

theorem section_scalarTower {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]
    (c : X ⟶ Spec (.of F)) (U : X.Opens) [Nonempty U] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    IsScalarTower F Γ(X, U) X.functionField := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change baseToFunctionField c a =
    (X.germToFunctionField U).hom ((Scheme.TwoAffineOpenCover.algebraOfHom c U).algebraMap a)
  symm
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change (c.appLE ⊤ U le_top ≫ X.germToFunctionField U).hom _ =
    (c.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom _
  congr 2
  delta Scheme.Hom.appLE
  rw [Category.assoc]
  erw [TopCat.Presheaf.germ_res]
  rfl

set_option backward.isDefEq.respectTransparency false in
def pullbackFunctionFieldEquiv (M : CurveModel K E) (V : M.C.TwoAffineOpenCover)
    [Nonempty V.U0] [Nonempty V.U1] [Nonempty (V.U0 ⊓ V.U1 : M.C.Opens)]
    (L : Type u) [Field L] [Algebra K L] [IsDomain (L ⊗[K] E)] :
    letI := SchemeModelGeometricIntegral.isIntegral_pullback M V L
    let c := pullback.snd M.toBase (Scheme.TwoAffineOpenCover.specMap K L)
    letI := (baseToFunctionField c).toAlgebra
    FractionRing (L ⊗[K] E) ≃ₐ[L]
      (pullback M.toBase (Scheme.TwoAffineOpenCover.specMap K L)).functionField := by
  letI := SchemeModelGeometricIntegral.isIntegral_pullback M V L
  let Y := pullback M.toBase (Scheme.TwoAffineOpenCover.specMap K L)
  let c := pullback.snd M.toBase (Scheme.TwoAffineOpenCover.specMap K L)
  let W := V.pullback M.toBase L
  letI := (baseToFunctionField c).toAlgebra
  letI := Scheme.TwoAffineOpenCover.algebraOfHom M.toBase V.U0
  letI : Algebra Γ(M.C, V.U0) E :=
    (SchemeModelGeometricIntegral.sectionToField M V.U0).toRingHom.toAlgebra
  haveI : IsScalarTower K Γ(M.C, V.U0) E :=
    IsScalarTower.of_algebraMap_eq fun k =>
      (SchemeModelGeometricIntegral.sectionToField M V.U0).commutes k |>.symm
  haveI : IsFractionRing Γ(M.C, V.U0) M.C.functionField :=
    functionField_isFractionRing_of_isAffineOpen M.C V.U0 V.isAffineOpen_U0
  let ef : M.C.functionField ≃ₐ[Γ(M.C, V.U0)] E :=
    { M.ffEquiv.symm with commutes' := fun _ => rfl }
  haveI : IsFractionRing Γ(M.C, V.U0) E :=
    IsLocalization.isLocalization_of_algEquiv _ ef
  haveI : IsDomain (L ⊗[K] Γ(M.C, V.U0)) :=
    SchemeModelGeometricIntegral.isDomain_tensor_sections M L V.U0
  haveI : IsDomain (L ⊗[K] (V.cover M.toBase).A0) :=
    SchemeModelGeometricIntegral.isDomain_tensor_sections M L V.U0
  haveI : IsDomain (L ⊗[K] (V.cover M.toBase).A1) :=
    SchemeModelGeometricIntegral.isDomain_tensor_sections M L V.U1
  haveI : IsDomain (L ⊗[K] (V.cover M.toBase).A01) :=
    SchemeModelGeometricIntegral.isDomain_tensor_sections M L (V.U0 ⊓ V.U1)
  obtain ⟨_, hn0, _⟩ := V.isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct M.toBase L
  haveI : Nonempty W.U0 := hn0
  let e0 := (V.exists_baseChangeIsos_structureSheaf M.toBase L).choose
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c W.U0
  haveI : IsFractionRing Γ(Y, W.U0) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y W.U0 W.isAffineOpen_U0
  haveI : IsScalarTower L Γ(Y, W.U0) Y.functionField := section_scalarTower c W.U0
  let e0' : (L ⊗[K] Γ(M.C, V.U0)) ≃ₐ[L] Γ(Y, W.U0) := e0
  let e : FractionRing (L ⊗[K] Γ(M.C, V.U0)) ≃ₐ[L] Y.functionField :=
    IsFractionRing.algEquivOfAlgEquiv e0'
  exact (tensorFractionEquiv K Γ(M.C, V.U0) E L).symm.trans e

#print axioms section_scalarTower
#print axioms pullbackFunctionFieldEquiv
end FourCorner.Slot03High
