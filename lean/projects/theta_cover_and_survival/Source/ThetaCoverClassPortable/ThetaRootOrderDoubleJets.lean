import ThetaCoverClassPortable.ThetaChartTangentVanishing
import ThetaCoverClassPortable.ThetaLiteralRootJets

namespace FourCorner.ThetaRootOrderDoubleJets
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDExactChartTransitions ThetaDActualDifferential
open ThetaRootCanonicalSections ThetaLineRootPointCharts ThetaProjectiveRootPlaceEmbedding
open ThetaChartTangentVanishing ThetaContactDifferentialDivisors ThetaActualLineDifferentials
open ThetaGeometricResidueCoordinates ThetaGeometricContactPoints ThetaLiteralBinaryRestrictions BinaryQuarticDoubleRoots
open SmoothProperRationalPointPlaces
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

 theorem affine_Y_factor (α β : K) :
    differential (.affine α β)=localEquation 1 (-α) 1 (-β) • (y • omega) := by
  rw [affine_eq,affineDifferential,affineGlobalSection_germ]
  congr 1
  change affineFunction α β=algebraMap K field (-α)*uY+algebraMap K field (1:K)*vY+algebraMap K field (-β)
  simp only [affineFunction,map_neg,map_one,one_mul]
  ring

 theorem affine_X_factor' (α β : K) :
    differential (.affine α β)=localEquation 0 (-β) 1 (-α) • (x • omega) := by
  rw [affine_X_factor]
  congr 1
  change v-algebraMap K field β*u-algebraMap K field α=
    algebraMap K field (-β)*u+algebraMap K field (1:K)*v+algebraMap K field (-α)
  simp only [map_neg,map_one,one_mul]
  ring

 theorem vertical_Z_factor (s : K) :
    differential (.vertical s)=localEquation 2 1 (-s) 0 • omega := by
  rw [vertical_eq,verticalDifferential,verticalGlobalSection_germ]
  congr 1
  change verticalFunction s=algebraMap K field (1:K)*x+algebraMap K field (-s)*y+algebraMap K field (0:K)
  simp [verticalFunction,sub_eq_add_neg]

 theorem yzero_Z_factor : differential .yzero=localEquation 2 0 1 0 • omega := by
  rw [yzero_eq]
  change y • omega=(algebraMap K field (0:K)*x+algebraMap K field (1:K)*y+algebraMap K field (0:K)) • omega
  simp

 theorem factor_nonzero (L : ThetaLine K) (f : field) (ζ : Ω[field⁄K])
    (he : differential L=f • ζ) : f≠0 := by
  intro hz
  have hn := ThetaRootCanonicalSections.nonzero L
  rw [he,hz,zero_smul] at hn
  exact hn rfl

 theorem finite_double_jet (L : ThetaLine K) (t : K) (ht : L.restrict t 1=0)
    (ho : 2≤(pointEquivRationalPlace toBase (finiteRootPoint L t ht)).val.ordDifferential (differential L)) :
    ZeroJet (restriction L) ![t,1] := by
  cases L with
  | affine α β =>
    have hz : thetaF t 1 (α*t+β)=0 := by simpa [ThetaLine.restrict] using ht
    have he := affine_Y_factor α β
    have hh := Y_tangent ![t,α*t+β] (affine_relations α β t hz) (-α) 1 (-β)
      (factor_nonzero _ _ _ he) (by rw [←he];exact ho)
    apply ThetaLiteralRootJets.affine_finite α β t hz
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,neg_neg,one_mul,add_comm] using hh
  | vertical s =>
    have hz : thetaF (s*t) t 1=0 := ht
    have he := vertical_Z_factor s
    have hh := Z_tangent ![s*t,t] (vertical_relations s t hz) 1 (-s) 0
      (factor_nonzero _ _ _ he) (by rw [←he];exact ho)
    apply ThetaLiteralRootJets.vertical_finite s t hz
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,one_mul,neg_mul,sub_neg_eq_add] using hh
  | yzero =>
    have hz : thetaF t 0 1=0 := ht
    have he := yzero_Z_factor
    have hh := Z_tangent ![t,0] (Z_relations t 0 hz) 0 1 0
      (factor_nonzero _ _ _ he) (by rw [←he];exact ho)
    apply ThetaLiteralRootJets.yzero_finite t hz
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,zero_mul,one_mul,zero_sub,neg_eq_zero] using hh

 theorem infinity_double_jet (L : ThetaLine K) (ht : L.restrict 1 0=0)
    (ho : 2≤(pointEquivRationalPlace toBase (infinityRootPoint L ht)).val.ordDifferential (differential L)) :
    ZeroJet (restriction L) ![1,0] := by
  cases L with
  | affine α β =>
    have hz : thetaF 1 0 α=0 := by simpa [ThetaLine.restrict] using ht
    have he := affine_X_factor' α β
    have hh := X_tangent ![0,α] (X_relations 0 α hz) (-β) 1 (-α)
      (factor_nonzero _ _ _ he) (by rw [←he];exact ho)
    apply ThetaLiteralRootJets.affine_infinity α β hz
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,one_mul] using hh
  | vertical s =>
    apply ThetaLiteralRootJets.vertical_infinity s
    simpa [ThetaLine.restrict] using ht
  | yzero => norm_num [ThetaLine.restrict,thetaF] at ht

/-- Native order at least two on the SAME actual Place implies the full
literal binary two-partial double jet, including infinity and all line charts. -/
theorem root_double_at (L : ThetaLine K) (P : Root L)
    (ho : 2≤(rootPlace L P).ordDifferential (differential L)) : DoubleAt (restriction L) P.val := by
  by_cases hi : P.val=infinity
  · rw [hi]
    apply (doubleAt_infinity_iff (homogeneous L)).mpr
    apply infinity_double_jet L (infinity_equation L P.val P.property hi)
    simpa only [rootPlace,rootPoint,dif_pos hi] using ho
  · rw [finiteParameter_spec P.val hi]
    apply (doubleAt_finite_iff (homogeneous L) _).mpr
    apply finite_double_jet L (finiteParameter P.val hi) (finite_equation L P.val P.property hi)
    simpa only [rootPlace,rootPoint,dif_neg hi] using ho

#print axioms finite_double_jet
#print axioms infinity_double_jet
#print axioms root_double_at
end
end FourCorner.ThetaRootOrderDoubleJets
