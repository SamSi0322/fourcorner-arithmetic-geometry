import ThetaCoverClassPortable.ThetaValuationTangencyOrder

namespace FourCorner.ThetaAffineContactOrder
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDExactChartTransitions
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

 theorem map_YFu {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) :
    f (YFu a b)=YFu (f a) (f b) := by
  simp only [YFu,map_mul,map_sub,map_add,map_pow,map_ofNat]

 theorem map_YFv {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) :
    f (YFv a b)=YFv (f a) (f b) := by
  simp only [YFv,map_mul,map_sub,map_add,map_pow,map_ofNat]

/-- At the ACTUAL place of a literal double contact, the ACTUAL original
line function has order ≥2. Stalk/residue evaluation, normal-unit and tangent
vanishing are DERIVED from the original scheme point and quartic restriction. -/
theorem affine_function_order_ge_two (α β z : K) (hz : thetaF z 1 (α*z+β)=0)
    (hd : (ThetaLinesPolynomialContacts.affineRestriction α β).derivative.eval z=0) :
    2≤(affinePlace α β z hz).ord (affineFunction α β) := by
  let vals : Fin 2 → K := ![z,α*z+β]
  let hv := affine_relations α β z hz
  let p := rationalPlace 1 vals hv
  let w := p.val
  let A := w.toValuationSubring
  let e : A →ₐ[K] K := evaluate w p.property
  let a : A := coordinateValue 1 vals hv 0
  let b : A := coordinateValue 1 vals hv 1
  have ha : (a:field)=uY := coordinateValue_coe 1 vals hv 0
  have hb : (b:field)=vY := coordinateValue_coe 1 vals hv 1
  have ea : e a=z := evaluate_coordinateValue 1 vals hv 0
  have eb : e b=α*z+β := evaluate_coordinateValue 1 vals hv 1
  have eα : e (algebraMap K A α)=α := e.commutes α
  have eβ : e (algebraMap K A β)=β := e.commutes β
  have hFu : e (YFu a b)=YFu z (α*z+β) := by
    exact (map_YFu e.toRingHom a b).trans (congrArg₂ YFu ea eb)
  have hFv : e (YFv a b)=YFv z (α*z+β) := by
    exact (map_YFv e.toRingHom a b).trans (congrArg₂ YFv ea eb)
  obtain ⟨hQ,hT⟩ := affine_normal_and_tangent α β z hz hd
  let q : A := YFv a b
  let n : A := YFu a b+algebraMap K A α*YFv a b
  let f : A := b-algebraMap K A α*a-algebraMap K A β
  have hqe : e q≠0 := by change e (YFv a b)≠0;rw [hFv];exact hQ
  have hqu : IsUnit q := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hm
    rw [←localEval_kernel e] at hm
    exact hqe hm
  have hnm : n∈IsLocalRing.maximalIdeal A := by
    rw [←localEval_kernel e]
    change e n=0
    simpa only [n,map_add,map_mul,hFu,hFv,eα] using hT
  have hfm : f∈IsLocalRing.maximalIdeal A := by
    rw [←localEval_kernel e]
    change e f=0
    simp only [f,map_sub,map_mul,ea,eb,eα,eβ]
    ring
  have hqc : (q:field)=YFv uY vY := by
    change YFv (a:field) (b:field)=_
    rw [ha,hb]
  have hnc : (n:field)=YFu uY vY+algebraMap K field α*YFv uY vY := by
    change YFu (a:field) (b:field)+((algebraMap K A α:A):field)*YFv (a:field) (b:field)=_
    rw [ha,hb,Place.coe_algebraMap]
  have hfc : (f:field)=affineFunction α β := by
    change (b:field)-((algebraMap K A α:A):field)*(a:field)-((algebraMap K A β:A):field)=_
    rw [ha,hb,Place.coe_algebraMap,Place.coe_algebraMap]
    rfl
  have hq0 : YFv uY vY≠0 := by
    intro hh
    apply hqu.ne_zero
    apply Subtype.ext
    change (q:field)=0
    rw [hqc,hh]
  have hD : KaehlerDifferential.D K field (f:field)=
      (-(n:field)/(q:field)) • KaehlerDifferential.D K field (a:field) := by
    rw [hfc,ha,hnc,hqc]
    exact affine_derivative_normal_form α β hq0
  have hf0 : (f:field)≠0 := by rw [hfc];exact affineFunction_ne_zero α β
  have hh := order_ge_two_of_normal_form w f a n q hf0 hfm hnm hqu hD
  rw [hfc] at hh
  exact hh

#print axioms affine_function_order_ge_two
end
end FourCorner.ThetaAffineContactOrder
