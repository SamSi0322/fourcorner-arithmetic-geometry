import ThetaCoverClassPortable.ThetaIsoFunctionField
import ThetaCoverClassPortable.ThetaFiniteGenericDegree
import ThetaCoverClassPortable.ThetaGeometricChartEvaluation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace FourCorner.ActualAffineChartFunctionField
variable {R : CommRingCat} [IsDomain R] {X : Scheme} [IsIntegral X]
  (j : Spec R ⟶ X) [IsOpenImmersion j]

def stalkIso : X.functionField ≅ (Spec R).functionField :=
  X.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint (Spec R)))

def fieldEquiv : X.functionField ≃+* (Spec R).functionField :=
  (stalkIso j).commRingCatIsoToRingEquiv

 theorem generic_diagram :
    Spec.map (CommRingCat.ofHom (fieldEquiv j).toRingHom) ≫ X.fromSpecStalk (genericPoint X)=
      (Spec R).fromSpecStalk (genericPoint (Spec R)) ≫ j := by
  change Spec.map (stalkIso j).hom ≫ X.fromSpecStalk (genericPoint X)=_
  simp only [stalkIso,Iso.trans_hom,asIso_hom,Spec.map_comp,Category.assoc,
    TopCat.Presheaf.stalkCongr_hom,Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk j

def chartMap : R →+* X.functionField :=
  (fieldEquiv j).symm.toRingHom.comp (algebraMap R (Spec R).functionField)

 theorem chart_diagram : Spec.map (CommRingCat.ofHom (chartMap j)) ≫ j=
    X.fromSpecStalk (genericPoint X) := by
  unfold chartMap
  rw [CommRingCat.ofHom_comp,Spec.map_comp]
  have hs : Spec.map (CommRingCat.ofHom (algebraMap R (Spec R).functionField))=
      (Spec R).fromSpecStalk (genericPoint (Spec R)) := by
    rw [Spec.fromSpecStalk_eq']
    rfl
  rw [Category.assoc,hs,←generic_diagram]
  rw [←Category.assoc,←Spec.map_comp,←CommRingCat.ofHom_comp]
  simp

def chartAlgebra : Algebra R X.functionField := (chartMap j).toAlgebra

 theorem chart_fractionRing : letI := chartAlgebra j; IsFractionRing R X.functionField := by
  letI := chartAlgebra j
  let e : (Spec R).functionField ≃ₐ[R] X.functionField :=
    AlgEquiv.ofRingEquiv (f:=(fieldEquiv j).symm) (fun _=>rfl)
  exact IsFractionRing.of_algEquiv e

 theorem chartMap_injective : Function.Injective (chartMap j) :=
  (fieldEquiv j).symm.injective.comp (IsFractionRing.injective R (Spec R).functionField)

 theorem chartMap_of_section (U : X.Opens) [Nonempty U]
    (e : (⊤ : (Spec R).Opens)≤j ⁻¹ᵁ U) (s : Γ(X,U)) (r : R)
    (hs : (j.appLE U ⊤ e).hom s=(Scheme.ΓSpecIso R).inv r) :
    chartMap j r=X.germToFunctionField U s := by
  apply (fieldEquiv j).injective
  simp only [chartMap,RingHom.comp_apply,RingEquiv.coe_toRingHom,RingEquiv.apply_symm_apply]
  have hh : X.germToFunctionField U ≫ (stalkIso j).hom=
      j.appLE U ⊤ e ≫ (Spec R).presheaf.germ ⊤ (genericPoint (Spec R)) trivial := by
    simp only [stalkIso,Iso.trans_hom,asIso_hom,←Category.assoc,
      TopCat.Presheaf.stalkCongr_hom]
    change (X.presheaf.germ U (genericPoint X) _ ≫
      X.presheaf.stalkSpecializes (.of_eq (genericPoint_eq_of_isOpenImmersion j))) ≫
        j.stalkMap (genericPoint (Spec R))=_
    rw [X.presheaf.germ_stalkSpecializes]
    exact ThetaGeometricChartEvaluation.germ_stalkMap_appLE j U ⊤ e _ trivial
  have he:=congrArg (fun f : Γ(X,U) ⟶ (Spec R).functionField=>f.hom s) hh
  change fieldEquiv j (X.germToFunctionField U s)=
    (Spec R).presheaf.germ ⊤ (genericPoint (Spec R)) trivial ((j.appLE U ⊤ e).hom s) at he
  rw [hs] at he
  have hc : algebraMap R (Spec R).functionField r=
      (Spec R).presheaf.germ ⊤ (genericPoint (Spec R)) trivial ((Scheme.ΓSpecIso R).inv r) := by
    have hm := Spec.map_injective ((Spec.fromSpecStalk_eq' R (genericPoint (Spec R))).symm.trans
      (Spec.fromSpecStalk_eq R (genericPoint (Spec R))))
    exact congrArg (fun f : R ⟶ (Spec R).functionField=>f.hom r) hm
  exact ((fieldEquiv j).apply_symm_apply (algebraMap R (Spec R).functionField r)).trans (hc.trans he.symm)

 theorem square_field_comm {S : CommRingCat} [IsDomain S] {Y : Scheme} [IsIntegral Y]
    (f : X ⟶ Y) [Surjective f] (i : Spec S ⟶ Y) [IsOpenImmersion i]
    (g : S →+* R) (hsq : j ≫ f=Spec.map (CommRingCat.ofHom g) ≫ i) :
    (ThetaNativeFunctionFieldMap.fieldMap f).comp (chartMap i)=(chartMap j).comp g := by
  have he : CommRingCat.ofHom ((ThetaNativeFunctionFieldMap.fieldMap f).comp (chartMap i))=
      CommRingCat.ofHom ((chartMap j).comp g) := by
    apply Spec.map_injective
    apply (cancel_mono i).mp
    calc
      Spec.map (CommRingCat.ofHom ((ThetaNativeFunctionFieldMap.fieldMap f).comp (chartMap i))) ≫ i=
          Spec.map (CommRingCat.ofHom (ThetaNativeFunctionFieldMap.fieldMap f)) ≫
            (Spec.map (CommRingCat.ofHom (chartMap i)) ≫ i) := by
              rw [CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
      _=Spec.map (CommRingCat.ofHom (ThetaNativeFunctionFieldMap.fieldMap f)) ≫
          Y.fromSpecStalk (genericPoint Y) := by rw [chart_diagram i]
      _=X.fromSpecStalk (genericPoint X) ≫ f := ThetaNativeFunctionFieldMap.generic_diagram f
      _=(Spec.map (CommRingCat.ofHom (chartMap j)) ≫ j) ≫ f := by rw [chart_diagram j]
      _=Spec.map (CommRingCat.ofHom (chartMap j)) ≫
          (Spec.map (CommRingCat.ofHom g) ≫ i) := by rw [Category.assoc,hsq]
      _=Spec.map (CommRingCat.ofHom ((chartMap j).comp g)) ≫ i := by
        rw [CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
  exact congrArg CommRingCat.Hom.hom he

#print axioms chart_diagram
#print axioms chart_fractionRing
end FourCorner.ActualAffineChartFunctionField
