import ThetaCoverClassPortable.ThetaCoverNativeQuadraticField
import ThetaCoverClassPortable.ThetaDNativeProjSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory MvPolynomial
namespace FourCorner.ThetaQQUnitRootFields
open ThetaLiteralModels ThetaDNativeProjRatios ThetaDNativeProjSections ThetaCoverRationalData
local instance : IsIntegral (D ℚ) := ThetaDPlaneChartSections.original_integral
abbrev F : Type := (D ℚ).functionField
local instance : Algebra ℚ F := (baseToFunctionField (dToBase ℚ)).toAlgebra
local instance : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
local instance (j : Fin 3) : Nonempty (B j) := basic_nonempty j

/-- The ACTUAL original affine chart ring mapped through its ACTUAL section
map and native generic stalk, not a coordinate replacement field. -/
def chartField (j : Fin 3) : ThetaQuotientCharts.R j →+* F :=
  ((D ℚ).germToFunctionField (B (ThetaQuotientCharts.targetIndex j))).hom.comp
    (sections (ThetaQuotientCharts.targetIndex j))
def eval (j : Fin 3) : ThetaQuotientCharts.RA →+* F :=
  (chartField j).comp (ThetaQuotientCharts.rq j).toRingHom

 theorem chartField_X (j : Fin 3) (a : Fin 2) :
    chartField j (Ideal.Quotient.mk _ (X a))=
      ratio (ThetaQuotientCharts.targetIndex j) (ThetaAmbientChart.insert 2 (ThetaQuotientCharts.targetIndex j) a) :=
  sections_coordinate_generic _ _

 theorem eval_C (j : Fin 3) (q : ℚ) : eval j (C q)=algebraMap ℚ F q := by
  exact RingHom.congr_fun (Subsingleton.elim ((eval j).comp (MvPolynomial.C : ℚ →+* ThetaQuotientCharts.RA))
    (algebraMap ℚ F)) q

 theorem eval_X (j : Fin 3) (a : Fin 2) : eval j (X a)=
      ratio (ThetaQuotientCharts.targetIndex j) (ThetaAmbientChart.insert 2 (ThetaQuotientCharts.targetIndex j) a) :=
  sections_coordinate_generic _ _

abbrev coordinateIndex : Fin 3 → Fin 3 := ![2,0,1]
 theorem eval_rcoords (j a : Fin 3) :
    eval j (ThetaQuotientCharts.rcoords j a)=ratio (ThetaQuotientCharts.targetIndex j) (coordinateIndex a) := by
  fin_cases j <;> fin_cases a <;>
    simp only [ThetaQuotientCharts.rcoords,ThetaQuotientCharts.targetIndex,coordinateIndex,
      Fin.isValue,eval_X,map_one]
    <;> change _ = ratio _ _
    <;> norm_num [ThetaAmbientChart.insert, Fin.succAbove, ratio_self] <;> rfl


/-- Actual QQ(D) coefficients for the original cover's two root charts.
The t branch is the literal source T/denominator; denominator=P,Q,R.
The u branch is the true original (z+shift*T)/denominator. -/
def s (j : Fin 3) : F := ratio (ThetaQuotientCharts.targetIndex j) 2
def a (j : Fin 3) : F := chartField j (ThetaQuotientCharts.a j)
def b (j : Fin 3) : F := chartField j (ThetaQuotientCharts.b j)
def c (j : Fin 3) : F := chartField j (ThetaQuotientCharts.c j)
def qT (j : Fin 3) : F := s j
def qU (j : Fin 3) : F := c j*s j/b j

 theorem b_image (j : Fin 3) : b j=s j^2*rationalH := by
  change eval j (ThetaQuotientCharts.bpoly j)=_
  unfold ThetaQuotientCharts.bpoly
  simp only [map_mul,map_add,map_sub,map_pow,map_ofNat,eval_C,eval_rcoords]
  norm_num only [map_div₀,map_one,map_ofNat]
  have hx := ratio_mul 2 (ThetaQuotientCharts.targetIndex j) 0
  have hy := ratio_mul 2 (ThetaQuotientCharts.targetIndex j) 1
  change ratio 2 0*s j=ratio (ThetaQuotientCharts.targetIndex j) 0 at hx
  change ratio 2 1*s j=ratio (ThetaQuotientCharts.targetIndex j) 1 at hy
  change (1/2:F)*(ratio (ThetaQuotientCharts.targetIndex j) 0^2+ratio (ThetaQuotientCharts.targetIndex j) 1^2-2*(s j)^2)=(s j)^2*rationalH
  rw [←hx,←hy]
  unfold rationalH
  ring

 theorem s_ne_zero (j : Fin 3) : s j≠0 := ratio_ne_zero _ _
 theorem b_ne_zero (j : Fin 3) : b j≠0 := by
  rw [b_image]
  exact mul_ne_zero (pow_ne_zero _ (s_ne_zero j)) rationalH_ne_zero

 theorem base_conic_image (j : Fin 3) : a j*b j=c j^2 := by
  have hh:=congrArg (chartField j) (ThetaQuotientCharts.base_conic j)
  simpa only [a,b,c,map_mul,map_pow] using hh

 theorem qT_square (j : Fin 3) : qT j^2*rationalH=b j := (b_image j).symm
 theorem qU_square (j : Fin 3) : qU j^2*rationalH=a j := by
  calc
    qU j^2*rationalH=(c j)^2*((s j)^2*rationalH)/(b j)^2 := by
      unfold qU
      simp only [div_eq_mul_inv]
      ring
    _=(c j)^2*b j/(b j)^2 := by rw [←b_image]
    _=a j := by
      rw [←base_conic_image]
      field_simp [b_ne_zero j] <;> ring

#print axioms b_image
#print axioms qU_square
end FourCorner.ThetaQQUnitRootFields
