import ThetaLocalLineDerivatives

namespace FourCorner.ThetaChartTangentVanishing
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDExactChartTransitions ThetaDFieldCoordinates ThetaDActualDifferential
open ThetaGeometricResidueCoordinates ThetaContactTangencyCertificates ThetaChartCanonicalFrames
open ThetaLocalLineDerivatives ThetaOrderTwoDerivativeEvaluation ResiduePlaceEvaluation
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

 def localEquation (j : Fin 3) (a b c : K) : field :=
  algebraMap K field a*coordinate j 0+algebraMap K field b*coordinate j 1+algebraMap K field c

 theorem linear_tangent (j : Fin 3) (vals : Fin 2→K)
    (hv : ∀i : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation j i)=0)
    (ζ : Ω[field⁄K]) (hζ : ζ≠0) (hframe : (rationalPlace j vals hv).val.ordDifferential ζ=0)
    (a b c : K) (hf : localEquation j a b c≠0)
    (d0 d1 : (rationalPlace j vals hv).val.toValuationSubring)
    (hd0 : KaehlerDifferential.D K field (coordinate j 0)=(d0:field) • ζ)
    (hd1 : KaehlerDifferential.D K field (coordinate j 1)=(d1:field) • ζ)
    (ho : 2≤(rationalPlace j vals hv).val.ordDifferential (localEquation j a b c • ζ)) :
    a*evaluate _ (rationalPlace j vals hv).property d0+
      b*evaluate _ (rationalPlace j vals hv).property d1=0 := by
  let p := rationalPlace j vals hv
  let A := p.val.toValuationSubring
  let n : A := algebraMap K A a*d0+algebraMap K A b*d1
  have hn : (n:field)=algebraMap K field a*(d0:field)+algebraMap K field b*(d1:field) := by
    change ((algebraMap K A a:A):field)*(d0:field)+((algebraMap K A b:A):field)*(d1:field)=_
    rw [Place.coe_algebraMap,Place.coe_algebraMap]
  have hD : KaehlerDifferential.D K field (localEquation j a b c)=(n:field) • ζ := by
    simp only [localEquation,map_add,Derivation.leibniz,Derivation.map_algebraMap,smul_zero,zero_add,hd0,hd1]
    rw [hn]
    module
  have hh := derivative_factor_evaluation p.val p.property _ hf
    (function_order_of_frame p.val _ hf ζ hζ hframe ho) ζ hζ hframe n hD
  change evaluate p.val p.property n=0 at hh
  have ea : evaluate p.val p.property (algebraMap K A a)=a := (evaluate p.val p.property).commutes a
  have eb : evaluate p.val p.property (algebraMap K A b)=b := (evaluate p.val p.property).commutes b
  simpa only [n,map_add,map_mul,ea,eb] using hh

 theorem X_tangent (vals : Fin 2→K)
    (hv : ∀i : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation 0 i)=0)
    (a b c : K) (hf : localEquation 0 a b c≠0)
    (ho : 2≤(rationalPlace 0 vals hv).val.ordDifferential (localEquation 0 a b c • (x • omega))) :
    a*YFv (vals 0) (vals 1)-b*YFu (vals 0) (vals 1)=0 := by
  let U := coordinateValue 0 vals hv 0
  let V := coordinateValue 0 vals hv 1
  have hu : (U:field)=u := coordinateValue_coe 0 vals hv 0
  have hvv : (V:field)=v := coordinateValue_coe 0 vals hv 1
  have h0 : KaehlerDifferential.D K field (coordinate 0 0)=(YFv U V:field) • (x • omega) := by
    change KaehlerDifferential.D K field u=YFv (U:field) (V:field) • (x • omega)
    rw [hu,hvv];exact Du
  have h1 : KaehlerDifferential.D K field (coordinate 0 1)=(-YFu U V:field) • (x • omega) := by
    change KaehlerDifferential.D K field v=(-YFu (U:field) (V:field)) • (x • omega)
    rw [hu,hvv];exact Dv
  have hh := linear_tangent 0 vals hv (x • omega) (smul_ne_zero x_ne_zero omega_ne_zero)
    (rational_X_frame vals hv) a b c hf (YFv U V) (-YFu U V) h0 h1 ho
  have e0 := evaluate_coordinateValue 0 vals hv 0
  have e1 := evaluate_coordinateValue 0 vals hv 1
  simpa only [U,V,YFu,YFv,map_mul,map_add,map_sub,map_pow,map_ofNat,map_neg,e0,e1,sub_eq_add_neg,mul_neg] using hh

 theorem Y_tangent (vals : Fin 2→K)
    (hv : ∀i : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation 1 i)=0)
    (a b c : K) (hf : localEquation 1 a b c≠0)
    (ho : 2≤(rationalPlace 1 vals hv).val.ordDifferential (localEquation 1 a b c • (y • omega))) :
    -a*YFv (vals 0) (vals 1)+b*YFu (vals 0) (vals 1)=0 := by
  let U := coordinateValue 1 vals hv 0
  let V := coordinateValue 1 vals hv 1
  have hu : (U:field)=uY := coordinateValue_coe 1 vals hv 0
  have hvv : (V:field)=vY := coordinateValue_coe 1 vals hv 1
  have h0 : KaehlerDifferential.D K field (coordinate 1 0)=(-YFv U V:field) • (y • omega) := by
    change KaehlerDifferential.D K field uY=(-YFv (U:field) (V:field)) • (y • omega)
    rw [hu,hvv];exact DuY
  have h1 : KaehlerDifferential.D K field (coordinate 1 1)=(YFu U V:field) • (y • omega) := by
    change KaehlerDifferential.D K field vY=YFu (U:field) (V:field) • (y • omega)
    rw [hu,hvv];exact DvY
  have hh := linear_tangent 1 vals hv (y • omega) (smul_ne_zero ThetaActualLineDifferentials.y_ne_zero omega_ne_zero)
    (rational_Y_frame vals hv) a b c hf (-YFv U V) (YFu U V) h0 h1 ho
  have e0 := evaluate_coordinateValue 1 vals hv 0
  have e1 := evaluate_coordinateValue 1 vals hv 1
  simpa only [U,V,YFu,YFv,map_mul,map_add,map_sub,map_pow,map_ofNat,map_neg,e0,e1,neg_mul,mul_neg] using hh

 theorem Z_tangent (vals : Fin 2→K)
    (hv : ∀i : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation 2 i)=0)
    (a b c : K) (hf : localEquation 2 a b c≠0)
    (ho : 2≤(rationalPlace 2 vals hv).val.ordDifferential (localEquation 2 a b c • omega)) :
    a*ZFy (vals 0) (vals 1)-b*ZFx (vals 0) (vals 1)=0 := by
  let U := coordinateValue 2 vals hv 0
  let V := coordinateValue 2 vals hv 1
  have hu : (U:field)=x := coordinateValue_coe 2 vals hv 0
  have hvv : (V:field)=y := coordinateValue_coe 2 vals hv 1
  have h0 : KaehlerDifferential.D K field (coordinate 2 0)=(ZFy U V:field) • omega := by
    change KaehlerDifferential.D K field x=ZFy (U:field) (V:field) • omega
    rw [hu,hvv];exact Dx
  have h1 : KaehlerDifferential.D K field (coordinate 2 1)=(-ZFx U V:field) • omega := by
    change KaehlerDifferential.D K field y=(-ZFx (U:field) (V:field)) • omega
    rw [hu,hvv];exact Dy
  have hh := linear_tangent 2 vals hv omega omega_ne_zero (rational_Z_frame vals hv)
    a b c hf (ZFy U V) (-ZFx U V) h0 h1 ho
  have e0 := evaluate_coordinateValue 2 vals hv 0
  have e1 := evaluate_coordinateValue 2 vals hv 1
  simpa only [U,V,ZFx,ZFy,map_mul,map_add,map_sub,map_pow,map_ofNat,map_neg,e0,e1,sub_eq_add_neg,mul_neg] using hh

#print axioms linear_tangent
#print axioms X_tangent
#print axioms Y_tangent
#print axioms Z_tangent
end
end FourCorner.ThetaChartTangentVanishing
