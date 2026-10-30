import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isAlgEquivZero_twistModule_fibre
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory NeronModelInfra
namespace FourCorner.PointKernelPairAlgEquiv
open RelPicard
variable {k : Type} [Field k] {X : Scheme} (c : X ⟶ Spec (.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] [LocallyOfFiniteType c]
    (P Q : SchemeHomOver (𝟙 (Spec (.of k))) c)

/-- The actual point-kernel modules, on the original curve itself, are
compared with the actual graph-divisor modules in the native point family. -/
theorem actual_point_pair : IsAlgEquivZero c (P.val.ker.invModule ⊗ Q.val.ker.module) := by
  let f := pullback.fst c (𝟙 (Spec (.of k)))
  have hp : P.val.ker.comap f=(RelEffCartierDiv.ofPoint c P.val P.property).I :=
    P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isAlgEquivZero_twistModule_fibre.AlgebraicGeometry.K2Aux.ker_comap_fst_eq_ofPoint_I c P.val P.property
  have hq : Q.val.ker.comap f=(RelEffCartierDiv.ofPoint c Q.val Q.property).I :=
    P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isAlgEquivZero_twistModule_fibre.AlgebraicGeometry.K2Aux.ker_comap_fst_eq_ofPoint_I c Q.val Q.property
  have hIp : P.val.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id P.val P.property
  have hIq : Q.val.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id Q.val Q.property
  have hIp' : (P.val.ker.comap f).IsInvertible := hp ▸ RelEffCartierDiv.isInvertible_I _
  have hIq' : (Q.val.ker.comap f).IsInvertible := hq ▸ RelEffCartierDiv.isInvertible_I _
  obtain ⟨ep⟩ := hIp.nonempty_pullback_invModule_iso f hIp'
  let eq : (Scheme.Modules.pullback f).obj Q.val.ker.module ≅ (Q.val.ker.comap f).module :=
    @asIso _ _ _ _ (Q.val.ker.pullbackModuleComparison f)
      (Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f hIq hIq')
  let e : (Scheme.Modules.pullback f).obj (P.val.ker.invModule ⊗ Q.val.ker.module) ≅
      pointSubBasepointModule (a:=c) P Q :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      ((ep ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hp)) ⊗ᵢ
       (eq ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module hq)))
  exact IsAlgEquivZero.of_iso_pointsSubBasepoint Q [P] (e ≪≫ (ρ_ _).symm)

#print axioms actual_point_pair
end FourCorner.PointKernelPairAlgEquiv
