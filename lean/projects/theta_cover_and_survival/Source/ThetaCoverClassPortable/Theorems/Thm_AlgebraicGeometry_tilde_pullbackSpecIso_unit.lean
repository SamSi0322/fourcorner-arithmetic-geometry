import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesTildePullback
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.tilde
noncomputable section
theorem pullbackSpecIso_unit {R S:CommRingCat.{u}} (φ:R⟶S) (N:ModuleCat.{u} R):
 ((tilde.adjunction (R:=R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app N ≫
  (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R:=R)).map (tilde.pullbackSpecIso φ N).hom ≫
  (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars φ.hom).obj N)) =
 (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app N ≫
  (ModuleCat.restrictScalars φ.hom).map ((tilde.adjunction (R:=S)).unit.app ((ModuleCat.extendScalars φ.hom).obj N)) := by
  let a₁:=(tilde.adjunction (R:=R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
  let a₂:=((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R:=S))).ofNatIsoRight
    (Scheme.Modules.pushforwardSpecCompΓIso φ).symm
  have h:=Adjunction.unit_leftAdjointUniq_hom_app a₁ a₂ N
  have hh:=congrArg (fun f=>f≫(Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
    (tilde ((ModuleCat.extendScalars φ.hom).obj N))) h
  have hc:a₂.unit.app N ≫(Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
      (tilde ((ModuleCat.extendScalars φ.hom).obj N)) =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app N ≫
        (ModuleCat.restrictScalars φ.hom).map ((tilde.adjunction (R:=S)).unit.app ((ModuleCat.extendScalars φ.hom).obj N)) := by
    change (((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app N ≫
      (ModuleCat.restrictScalars φ.hom).map ((tilde.adjunction (R:=S)).unit.app ((ModuleCat.extendScalars φ.hom).obj N))) ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).inv.app (tilde ((ModuleCat.extendScalars φ.hom).obj N))) ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars φ.hom).obj N)) =_
    rw [Category.assoc,Iso.inv_hom_id_app]
    erw [Category.comp_id]
  exact (Category.assoc _ _ _).symm.trans (hh.trans hc)

#print axioms pullbackSpecIso_unit
end
end AlgebraicGeometry.tilde
