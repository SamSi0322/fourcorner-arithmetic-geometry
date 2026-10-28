import ThetaAffineContactOrder

namespace FourCorner.ThetaVerticalContactOrder
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDFieldCoordinates
open ThetaGeometricContactPoints ThetaGeometricResidueCoordinates ThetaContactTangencyCertificates
open ThetaActualLineDifferentials ThetaValuationTangencyOrder
open SmoothProperRationalPointPlaces SchemePointStalkEvaluation ResiduePlaceEvaluation
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

 theorem map_ZFx {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) :
    f (ZFx a b)=ZFx (f a) (f b) := by
  simp only [ZFx,map_mul,map_sub,map_add,map_pow,map_ofNat]

 theorem map_ZFy {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) :
    f (ZFy a b)=ZFy (f a) (f b) := by
  simp only [ZFy,map_mul,map_sub,map_add,map_pow,map_ofNat]

/-- The vertical original projective-line function has true contact order
at least two at the ACTUAL original-curve place of its double root. -/
theorem vertical_function_order_ge_two (t z : K) (hz : thetaF (t*z) z 1=0)
    (hd : (ThetaLinesPolynomialContacts.verticalRestriction t).derivative.eval z=0) :
    2≤(verticalPlace t z hz).ord (verticalFunction t) := by
  let vals : Fin 2 → K := ![t*z,z]
  let hv := vertical_relations t z hz
  let p := rationalPlace 2 vals hv
  let w := p.val
  let A := w.toValuationSubring
  let e : A →ₐ[K] K := evaluate w p.property
  let a : A := coordinateValue 2 vals hv 0
  let b : A := coordinateValue 2 vals hv 1
  have ha : (a:field)=x := coordinateValue_coe 2 vals hv 0
  have hb : (b:field)=y := coordinateValue_coe 2 vals hv 1
  have ea : e a=t*z := evaluate_coordinateValue 2 vals hv 0
  have eb : e b=z := evaluate_coordinateValue 2 vals hv 1
  have et : e (algebraMap K A t)=t := e.commutes t
  have hFx : e (ZFx a b)=ZFx (t*z) z :=
    (map_ZFx e.toRingHom a b).trans (congrArg₂ ZFx ea eb)
  have hFy : e (ZFy a b)=ZFy (t*z) z :=
    (map_ZFy e.toRingHom a b).trans (congrArg₂ ZFy ea eb)
  obtain ⟨hQ,hT⟩ := vertical_normal_and_tangent t z hz hd
  let q : A := ZFx a b
  let n : A := ZFy a b+algebraMap K A t*ZFx a b
  let f : A := a-algebraMap K A t*b
  have hqe : e q≠0 := by change e (ZFx a b)≠0;rw [hFx];exact hQ
  have hqu : IsUnit q := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hm
    rw [←localEval_kernel e] at hm
    exact hqe hm
  have hnm : n∈IsLocalRing.maximalIdeal A := by
    rw [←localEval_kernel e]
    change e n=0
    simp only [n,map_add,map_mul,hFx,hFy,et]
    linear_combination hT
  have hfm : f∈IsLocalRing.maximalIdeal A := by
    rw [←localEval_kernel e]
    change e f=0
    simp only [f,map_sub,map_mul,ea,eb,et]
    ring
  have hqc : (q:field)=ZFx x y := by
    change ZFx (a:field) (b:field)=_
    rw [ha,hb]
  have hnc : (n:field)=ZFy x y+algebraMap K field t*ZFx x y := by
    change ZFy (a:field) (b:field)+((algebraMap K A t:A):field)*ZFx (a:field) (b:field)=_
    rw [ha,hb,Place.coe_algebraMap]
  have hfc : (f:field)=verticalFunction t := by
    change (a:field)-((algebraMap K A t:A):field)*(b:field)=_
    rw [ha,hb,Place.coe_algebraMap]
    rfl
  have hq0 : ZFx x y≠0 := by
    intro hh
    apply hqu.ne_zero
    apply Subtype.ext
    change (q:field)=0
    rw [hqc,hh]
  have hD : KaehlerDifferential.D K field (f:field)=
      (-(n:field)/(q:field)) • KaehlerDifferential.D K field (b:field) := by
    rw [hfc,hb,hnc,hqc]
    exact vertical_derivative_normal_form t hq0
  have hf0 : (f:field)≠0 := by rw [hfc];exact verticalFunction_ne_zero t
  have hh := order_ge_two_of_normal_form w f b n q hf0 hfm hnm hqu hD
  rw [hfc] at hh
  exact hh

#print axioms vertical_function_order_ge_two
end
end FourCorner.ThetaVerticalContactOrder
