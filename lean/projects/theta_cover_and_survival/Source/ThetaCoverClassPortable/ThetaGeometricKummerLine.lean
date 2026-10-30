import ThetaCoverClassPortable.ThetaQQKummerLine
import ThetaCoverClassPortable.NativeFieldMapSections
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso
import ThetaCoverClassPortable.ThetaCoverClass

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
namespace FourCorner.ThetaGeometricKummerLine
open ThetaLiteralModels ThetaDGeometricModel ThetaQQUnitRootOpens
local instance : IsIntegral (D ℚ) := ThetaDPlaneChartSections.original_integral
local instance : IsIntegral geometricD := geometric_integral
local instance : Surjective qb := ThetaDChartNaturality.qb_surjective
abbrev projection : geometricD ⟶ D ℚ := pullback.fst (dToBase ℚ) qb
local instance : Surjective projection := inferInstance
abbrev V (i : NonemptyIndex) : geometricD.Opens := projection ⁻¹ᵁ W i
instance (i : NonemptyIndex) : Nonempty (V i) := by
  obtain ⟨y⟩ := (inferInstance : Nonempty (W i))
  obtain ⟨x,hx⟩ := projection.surjective y.val
  exact ⟨⟨x,by change projection x∈W i;rw [hx];exact y.property⟩⟩

instance pair_nonempty (i j : NonemptyIndex) : Nonempty ((V i ⊓ V j : geometricD.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
instance original_pair_nonempty (i j : NonemptyIndex) : Nonempty ((W i ⊓ W j : (D ℚ).Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _

def roots (i : NonemptyIndex) : field := ThetaNativeFunctionFieldMap.fieldMap projection (ThetaQQKummerLine.roots i)
def units (i : NonemptyIndex) : Γ(geometricD,V i)ˣ := Units.map (projection.app (W i)).hom.toMonoidHom (ThetaQQKummerLine.units i)
def cc : UnitCocycle V := ThetaQQKummerLine.transitionCocycle.comap projection

def L : geometricD.Modules := (Scheme.Modules.pullback projection).obj ThetaQQKummerLine.L

theorem actual_pullback_glue :
    ∃e : L ≅ glueOfCocycle cc,∀i,e.hom.app (V i)
      (pullbackLocalSection projection (glueFrame ThetaQQKummerLine.transitionCocycle i))=glueFrame cc i :=
  exists_pullback_glueOfCocycle_iso projection nonempty_cover ThetaQQKummerLine.transitionCocycle

theorem cover : ⨆i,V i=⊤ := by
  change (⨆i,projection ⁻¹ᵁ W i)=⊤
  rw [←Scheme.Hom.preimage_iSup,nonempty_cover]
  rfl

theorem root_ne_zero (i : NonemptyIndex) : roots i≠0 :=
  (map_ne_zero (ThetaNativeFunctionFieldMap.fieldMap projection)).mpr
    (KummerUnitCocycle.root_ne_zero W ThetaCoverRationalData.rationalH ThetaQQKummerLine.roots ThetaQQKummerLine.units ThetaQQKummerLine.units_square i)

theorem units_square (i : NonemptyIndex) :
    algebraMap Γ(geometricD,V i) field (units i:Γ(geometricD,V i))=roots i^2*ThetaCoverFunctions.h := by
  change algebraMap Γ(geometricD,projection ⁻¹ᵁ W i) geometricD.functionField
    (projection.app (W i) (ThetaQQKummerLine.units i:Γ(D ℚ,W i)))=_
  rw [←NativeFieldMapSections.fieldMap_germ,ThetaQQKummerLine.units_square,
    map_mul,map_pow,ThetaCoverRationalData.rationalH_image]
  rfl

theorem transition_field (i j : NonemptyIndex) :
    algebraMap Γ(geometricD,V i ⊓ V j) field (cc.u i j)=roots j/roots i := by
  letI : Nonempty (projection ⁻¹ᵁ (W i ⊓ W j)) := pair_nonempty i j
  change algebraMap Γ(geometricD,projection ⁻¹ᵁ (W i ⊓ W j)) field
    (projection.app (W i ⊓ W j) (ThetaQQKummerLine.transitionCocycle.u i j))=_
  rw [←NativeFieldMapSections.fieldMap_germ,ThetaQQKummerLine.transition_native_field,map_div₀]
  rfl

#print axioms actual_pullback_glue
#print axioms units_square
#print axioms transition_field
end FourCorner.ThetaGeometricKummerLine
