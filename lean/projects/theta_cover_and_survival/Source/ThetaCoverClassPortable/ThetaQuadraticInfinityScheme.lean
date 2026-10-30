import ThetaCoverClassPortable.ActualClosedPointNativePlace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace FourCorner.ThetaQuadraticInfinityScheme
open ThetaQuadraticCurve
abbrev rationalResidueField := ThetaQuadraticInfinityQQ.residueField
abbrev residueField := QuadraticAlgebra F (algebraMap ℚ F (-2)) (algebraMap ℚ F 0)
instance irreducible : Fact (∀ z : F,z^2 ≠ algebraMap ℚ F (-2)+algebraMap ℚ F 0*z) := by
  constructor
  intro z h
  simp only [map_neg,map_ofNat,map_zero,zero_mul,add_zero] at h
  have hr := congrArg QuadraticAlgebra.re h
  norm_num [pow_two,QuadraticAlgebra.re_mul,QuadraticAlgebra.re_neg,
    QuadraticAlgebra.re_ofNat] at hr
  nlinarith [sq_nonneg z.re,sq_nonneg z.im]

theorem residue_degree : Module.finrank F residueField=2 := QuadraticAlgebra.finrank_eq_two _ _
abbrev tensorEquiv : (F ⊗[ℚ] rationalResidueField) ≃ₐ[F] residueField :=
  ActualQuadraticTensorBaseChange.equivalence (-2) 0
abbrev rationalBaseMap := Scheme.TwoAffineOpenCover.specMap ℚ rationalResidueField
abbrev tensorBase := pullback baseMap rationalBaseMap

def specTensorIso : Spec (.of residueField) ≅ tensorBase :=
  (Scheme.Spec.mapIso tensorEquiv.toRingEquiv.toCommRingCatIso.op) ≪≫
    (pullbackSpecIso ℚ F rationalResidueField).symm

abbrev fibreSource (branch : Bool) := pullback (ThetaQuadraticInfinityQQ.point branch) toRational
abbrev baseSource := pullback rationalBaseMap baseMap

def baseSourceToCurve (branch : Bool) : baseSource ⟶ curve :=
  pullback.lift (pullback.fst rationalBaseMap baseMap ≫ ThetaQuadraticInfinityQQ.point branch)
    (pullback.snd rationalBaseMap baseMap) (by
      rw [Category.assoc,ThetaQuadraticInfinityQQ.point_over]
      exact pullback.condition)

def fibreIso (branch : Bool) : fibreSource branch ≅ baseSource where
  hom := pullback.lift (pullback.fst (ThetaQuadraticInfinityQQ.point branch) toRational)
    (pullback.snd (ThetaQuadraticInfinityQQ.point branch) toRational ≫ toBase) (by
      have ho : ThetaQuadraticInfinityQQ.point branch ≫ ThetaLiteralModels.dToBase ℚ=rationalBaseMap :=
        ThetaSourceComparison.rational_base_unique _ _
      rw [←ho,←Category.assoc,pullback.condition,
        Category.assoc,pullback.condition]
      simp only [toBase,Category.assoc])
  inv := pullback.lift (pullback.fst rationalBaseMap baseMap) (baseSourceToCurve branch) (by
    simp [baseSourceToCurve,toRational])
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · apply pullback.hom_ext
      · simpa [baseSourceToCurve,toRational,Category.assoc] using
          (pullback.condition (f:=ThetaQuadraticInfinityQQ.point branch) (g:=toRational))
      · simp [baseSourceToCurve,toBase,Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp [baseSourceToCurve,toBase,Category.assoc]

@[reassoc (attr := simp)] theorem fibreIso_inv_toBase (branch : Bool) :
    (fibreIso branch).inv ≫ pullback.snd (ThetaQuadraticInfinityQQ.point branch) toRational ≫ toBase=
      pullback.snd rationalBaseMap baseMap := by
  simp [fibreIso,baseSourceToCurve,toBase,Category.assoc]

def point (branch : Bool) : Spec (.of residueField) ⟶ curve :=
  specTensorIso.hom ≫ (pullbackSymmetry baseMap rationalBaseMap).hom ≫
    (fibreIso branch).inv ≫ pullback.snd (ThetaQuadraticInfinityQQ.point branch) toRational

theorem point_over (branch : Bool) : point branch ≫ toBase=
    Spec.map (CommRingCat.ofHom (algebraMap F residueField)) := by
  simp only [point,Category.assoc,fibreIso_inv_toBase,pullbackSymmetry_hom_comp_snd]
  simp only [specTensorIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,pullbackSpecIso_inv_fst]
  change Spec.map (CommRingCat.ofHom tensorEquiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[ℚ] rationalResidueField))) = _
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext tensorEquiv.commutes

theorem point_closedImmersion (branch : Bool) : IsClosedImmersion (point branch) := by
  letI := ThetaQuadraticInfinityQQ.point_closedImmersion branch
  unfold point
  infer_instance

local instance : IsIntegral curve := curve_integral
local instance : IsProper toBase := curve_proper
local instance : SmoothOfRelativeDimension 1 toBase := curve_smooth
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra
local instance (branch : Bool) : IsClosedImmersion (point branch) := point_closedImmersion branch

def place (branch : Bool) : Place F functionField := ActualClosedPointNativePlace.nativePlace toBase (point branch)
theorem place_degree (branch : Bool) : (place branch).deg=2 := by
  rw [place,ActualClosedPointNativePlace.nativePlace_degree toBase (point branch) (point_over branch)]
  exact residue_degree

/-- The native closed Weil cycle obtained from the two literal Z=0
quadratic closed points. Hyperplane/order comparison is a further theorem. -/
def H2 : Divisor F functionField :=
  ActualClosedPointNativePlace.cycle toBase (point true)+
    ActualClosedPointNativePlace.cycle toBase (point false)

theorem H2_effective : 0≤H2 := add_nonneg
  (ActualClosedPointNativePlace.cycle_effective toBase (point true))
  (ActualClosedPointNativePlace.cycle_effective toBase (point false))
theorem H2_degree : Divisor.degree H2=4 := by
  rw [H2,map_add,
    ActualClosedPointNativePlace.cycle_degree toBase (point true) (point_over true),
    ActualClosedPointNativePlace.cycle_degree toBase (point false) (point_over false),residue_degree]
  norm_num

end FourCorner.ThetaQuadraticInfinityScheme
