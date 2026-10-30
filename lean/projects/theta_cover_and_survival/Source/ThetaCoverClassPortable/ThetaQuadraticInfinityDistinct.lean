import ThetaCoverClassPortable.ThetaQuadraticBoundaryHalfOrder
import ThetaCoverClassPortable.ThetaQuadraticDivisorPositivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial

namespace FourCorner.ThetaQuadraticInfinityDistinct
open ThetaQuadraticCurve
abbrev QQRes := ThetaQuadraticInfinityQQ.residueField

theorem rational_points_distinct :
    ThetaQuadraticInfinityQQ.point true (IsLocalRing.closedPoint QQRes) ≠
      ThetaQuadraticInfinityQQ.point false (IsLocalRing.closedPoint QQRes) := by
  intro h
  letI : IsOpenImmersion (ThetaDPlaneChartSections.chartMap 0) := by
    unfold ThetaDPlaneChartSections.chartMap
    infer_instance
  change ThetaDPlaneChartSections.chartMap 0
      (Spec.map (CommRingCat.ofHom (ThetaQuadraticInfinityQQ.evaluation true).toRingHom)
        (IsLocalRing.closedPoint QQRes)) =
    ThetaDPlaneChartSections.chartMap 0
      (Spec.map (CommRingCat.ofHom (ThetaQuadraticInfinityQQ.evaluation false).toRingHom)
        (IsLocalRing.closedPoint QQRes)) at h
  have hs := (ThetaDPlaneChartSections.chartMap 0).isOpenEmbedding.injective h
  let q : ThetaDPlaneChartSections.chartRing 0 :=
    Ideal.Quotient.mk _ (C 99*X 0^2-C 2*X 0+C 99)
  have heval (b : Bool) : ThetaQuadraticInfinityQQ.evaluation b q =
      99*(ThetaQuadraticInfinityQQ.parameter b)^2-2*ThetaQuadraticInfinityQQ.parameter b+99 := by
    simp [q,ThetaQuadraticInfinityQQ.evaluation,ThetaQuadraticInfinityQQ.values]
  have hp : ThetaQuadraticInfinityQQ.evaluation true q=0 := by
    rw [heval]
    simpa only [ThetaQuadraticInfinityQQ.sign,if_true,map_one,mul_one] using
      ThetaQuadraticInfinityQQ.quadratic_relation true
  have hq : ThetaQuadraticInfinityQQ.evaluation false q=0 := by
    have hh := congrArg PrimeSpectrum.asIdeal hs
    have ht : q ∈ (Spec.map (CommRingCat.ofHom (ThetaQuadraticInfinityQQ.evaluation true).toRingHom)
        (IsLocalRing.closedPoint QQRes)).asIdeal := by
      change ThetaQuadraticInfinityQQ.evaluation true q∈(IsLocalRing.maximalIdeal QQRes)
      rw [hp]
      exact Ideal.zero_mem _
    rw [hh] at ht
    change ThetaQuadraticInfinityQQ.evaluation false q∈(IsLocalRing.maximalIdeal QQRes) at ht
    simpa using ht
  have hm := ThetaQuadraticInfinityQQ.quadratic_relation false
  simp only [ThetaQuadraticInfinityQQ.sign,Bool.false_eq_true,if_false,map_neg,map_one] at hm
  rw [heval] at hq
  have hu : ThetaQuadraticInfinityQQ.parameter false=0 := by
    linear_combination (1/4)*hm-(1/4)*hq
  rw [hu] at hq
  norm_num at hq

theorem point_original_image (b : Bool) :
    toRational (ThetaQuadraticInfinityScheme.point b
      (IsLocalRing.closedPoint ThetaQuadraticInfinityScheme.residueField))=
      ThetaQuadraticInfinityQQ.point b (IsLocalRing.closedPoint QQRes) := by
  let z : ThetaQuadraticInfinityScheme.fibreSource b :=
    (ThetaQuadraticInfinityScheme.fibreIso b).inv
      ((pullbackSymmetry baseMap ThetaQuadraticInfinityScheme.rationalBaseMap).hom
        (ThetaQuadraticInfinityScheme.specTensorIso.hom
          (IsLocalRing.closedPoint ThetaQuadraticInfinityScheme.residueField)))
  have h := congrArg (fun f : ThetaQuadraticInfinityScheme.fibreSource b ⟶ ThetaLiteralModels.D ℚ => f z)
    (pullback.condition (f:=ThetaQuadraticInfinityQQ.point b) (g:=toRational))
  change ThetaQuadraticInfinityQQ.point b
      (pullback.fst (ThetaQuadraticInfinityQQ.point b) toRational z)=
    toRational (pullback.snd (ThetaQuadraticInfinityQQ.point b) toRational z) at h
  change toRational (pullback.snd (ThetaQuadraticInfinityQQ.point b) toRational z)=_
  rw [←h]
  congr 1
  exact Subsingleton.elim _ _

theorem points_distinct :
    ThetaQuadraticInfinityScheme.point true (IsLocalRing.closedPoint ThetaQuadraticInfinityScheme.residueField) ≠
      ThetaQuadraticInfinityScheme.point false (IsLocalRing.closedPoint ThetaQuadraticInfinityScheme.residueField) := by
  intro h
  have hh := congrArg toRational h
  rw [point_original_image,point_original_image] at hh
  exact rational_points_distinct hh

local instance : IsIntegral curve := curve_integral
local instance : IsProper toBase := curve_proper
local instance : SmoothOfRelativeDimension 1 toBase := curve_smooth
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra

theorem places_distinct : ThetaQuadraticInfinityScheme.place true ≠ ThetaQuadraticInfinityScheme.place false := by
  intro h
  apply points_distinct
  have hh := SmoothProperClosedPointPlaces.placeOfClosedPoint_injective toBase h
  exact congrArg Subtype.val hh

end FourCorner.ThetaQuadraticInfinityDistinct
