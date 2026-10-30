import ThetaCoverClassPortable.ActualLocalDVRFieldOrder
import Mathlib.AlgebraicGeometry.Morphisms.Integral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits

namespace FourCorner.ThetaQuadraticPlacePullback
open ThetaQuadraticCurve ThetaQuadraticField SmoothProperClosedPointPlaces
abbrev K := ThetaDGeometricModel.K
local instance : Algebra F K := coefficientEmbedding.toRingHom.toAlgebra
local instance : IsScalarTower ℚ F K :=
  IsScalarTower.of_algebraMap_eq (fun q => (coefficientEmbedding.commutes q).symm)

/-- Algebraicity is asserted only for the CONSTANT fields F -> Qbar. -/
theorem constantExtension_integral : IsIntegralHom extensionMap := by
  letI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K:=ℚ) F
  rw [IsIntegralHom.SpecMap_iff]
  change (algebraMap F K).IsIntegral
  rw [algebraMap_isIntegral_iff]
  infer_instance

theorem geometricProjection_integral : IsIntegralHom geometricProjection := by
  have he : geometricProjection=geometricBaseChangeIso.inv ≫ pullback.fst toBase extensionMap := by
    simp [geometricBaseChangeIso]
  rw [he]
  letI := constantExtension_integral
  infer_instance

def imageClosedPoint (x : closedPoints ThetaDGeometricModel.geometricD) : closedPoints curve :=
  ⟨geometricProjection x.val,by
    letI := geometricProjection_integral
    have h := geometricProjection.isClosedMap _ x.property
    simpa using h⟩

local instance : IsIntegral curve := curve_integral
local instance : IsProper toBase := curve_proper
local instance : SmoothOfRelativeDimension 1 toBase := curve_smooth
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra
local instance : IsIntegral ThetaDGeometricModel.geometricD := ThetaDGeometricModel.geometric_integral
local instance : IsProper ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_proper
local instance : SmoothOfRelativeDimension 1 ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_smooth
local instance : Algebra K ThetaDGeometricModel.field := ThetaDGeometricModel.fieldAlgebra
local instance : Surjective geometricProjection := geometricProjection_surjective

theorem imageClosedPoint_surjective : Function.Surjective imageClosedPoint := by
  letI : JacobsonSpace ThetaDGeometricModel.geometricD :=
    LocallyOfFiniteType.jacobsonSpace ThetaDGeometricModel.toBase
  intro y
  obtain ⟨z,hz⟩ := geometricProjection.surjective y.val
  have hclosed : IsClosed (geometricProjection ⁻¹' ({y.val} : Set curve)) :=
    y.property.preimage geometricProjection.continuous
  have hnonempty : (geometricProjection ⁻¹' ({y.val} : Set curve)).Nonempty :=
    ⟨z,hz⟩
  obtain ⟨x,hx,hxc⟩ := nonempty_inter_closedPoints hnonempty hclosed.isLocallyClosed
  exact ⟨⟨x,hxc⟩,Subtype.ext hx⟩

abbrev sourcePlace (x : closedPoints ThetaDGeometricModel.geometricD) : Place F functionField :=
  placeOfClosedPoint toBase (imageClosedPoint x)
abbrev geometricPlace (x : closedPoints ThetaDGeometricModel.geometricD) : Place K ThetaDGeometricModel.field :=
  placeOfClosedPoint ThetaDGeometricModel.toBase x

theorem sourcePlace_surjective : Function.Surjective sourcePlace := by
  intro v
  obtain ⟨y,rfl⟩ := placeOfClosedPoint_surjective toBase v
  obtain ⟨x,rfl⟩ := imageClosedPoint_surjective y
  exact ⟨x,rfl⟩

/-- Actual map of DVRs, induced by the actual scheme stalk map. -/
def valuationMap (x : closedPoints ThetaDGeometricModel.geometricD) :
    (sourcePlace x).toValuationSubring →+* (geometricPlace x).toValuationSubring :=
  (stalkValuationEquiv ThetaDGeometricModel.toBase x).toRingHom.comp
    ((geometricProjection.stalkMap x.val).hom.comp
      (stalkValuationEquiv toBase (imageClosedPoint x)).symm.toRingHom)

instance valuationMap_local (x : closedPoints ThetaDGeometricModel.geometricD) :
    IsLocalHom (valuationMap x) := by
  constructor
  intro z hz
  let eG := stalkValuationEquiv ThetaDGeometricModel.toBase x
  let eF := stalkValuationEquiv toBase (imageClosedPoint x)
  haveI : IsLocalHom (geometricProjection.stalkMap x.val).hom := geometricProjection.prop x.val
  change IsUnit (eG ((geometricProjection.stalkMap x.val).hom (eF.symm z))) at hz
  have h1 : IsUnit ((geometricProjection.stalkMap x.val).hom (eF.symm z)) := by
    have h := hz.map eG.symm.toMonoidHom
    change IsUnit (eG.symm (eG ((geometricProjection.stalkMap x.val).hom (eF.symm z)))) at h
    simpa only [RingEquiv.symm_apply_apply] using h
  have h2 : IsUnit (eF.symm z) :=
    IsUnit.of_map (geometricProjection.stalkMap x.val).hom (eF.symm z) h1
  have h3 := h2.map eF.toMonoidHom
  change IsUnit (eF (eF.symm z)) at h3
  simpa only [RingEquiv.apply_symm_apply] using h3

theorem valuationMap_field (x : closedPoints ThetaDGeometricModel.geometricD)
    (z : (sourcePlace x).toValuationSubring) :
    toGeometric (z:functionField)=(valuationMap x z:ThetaDGeometricModel.field) := by
  let a := (stalkValuationEquiv toBase (imageClosedPoint x)).symm z
  have he : algebraMap (curve.presheaf.stalk (imageClosedPoint x).val) functionField a=(z:functionField) := by
    rw [←stalkValuationEquiv_coe toBase (imageClosedPoint x) a]
    simp [a]
  change toGeometric (z:functionField)=
    ((stalkValuationEquiv ThetaDGeometricModel.toBase x
      ((geometricProjection.stalkMap x.val).hom a)) : ThetaDGeometricModel.field)
  rw [←he]
  exact (ThetaEtaleAllPlaces.stalk_field_naturality geometricProjection x.val a).trans
    (stalkValuationEquiv_coe ThetaDGeometricModel.toBase x _).symm

/-- Positive order scaling at EVERY actual geometric closed point, with
its actual closed image on D_F. No false IsCurveOver F Qbar(D) is used. -/
theorem actual_order_scale (x : closedPoints ThetaDGeometricModel.geometricD) :
    ∃ e : ℤ,0<e ∧ ∀ f : functionField,
      (geometricPlace x).ord (toGeometric f)=e*(sourcePlace x).ord f :=
  ActualLocalDVRFieldOrder.exists_positive_order_scale
    (sourcePlace x) (geometricPlace x) toGeometric (valuationMap x) (valuationMap_field x)

theorem actual_orders_equal_of_order_one (x : closedPoints ThetaDGeometricModel.geometricD)
    (t : functionField) (ht : 0<(sourcePlace x).ord t)
    (ht' : (geometricPlace x).ord (toGeometric t)=1) :
    ∀ f : functionField,(geometricPlace x).ord (toGeometric f)=(sourcePlace x).ord f :=
  ActualLocalDVRFieldOrder.order_eq_of_regular_positive_and_image_order_one
    (sourcePlace x) (geometricPlace x) toGeometric (valuationMap x) (valuationMap_field x) t ht ht'

end FourCorner.ThetaQuadraticPlacePullback
