import ThetaCoverClassPortable.ThetaActualHalfCanonicalContacts

namespace FourCorner.ThetaCanonicalLinePointValues
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDExactChartTransitions
open ThetaDActualDifferential ThetaDCanonicalPlaneBasis ThetaDPlaneRegularForms
open ThetaDNaturalGlobalDifferentials ThetaContactDifferentialDivisors ThetaActualLineDifferentials
open ThetaGeometricResidueCoordinates SmoothProperRationalPointPlaces SchemePointStalkEvaluation ResiduePlaceEvaluation
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance : Module K Γ(toBase.kaehler,⊤) :=
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler ⊤

def lineSection (a : Fin 3 → K) : Γ(toBase.kaehler,⊤) :=
  planeGlobalSectionEquiv (dotProductEquiv K (Fin 3) a)
def lineDifferential (a : Fin 3 → K) : Ω[field⁄K] := genericGerm (lineSection a)
def YEquation (a : Fin 3 → K) : field :=
  algebraMap K field (a 0)*uY+algebraMap K field (a 1)+algebraMap K field (a 2)*vY
def ZEquation (a : Fin 3 → K) : field :=
  algebraMap K field (a 2)+algebraMap K field (a 0)*x+algebraMap K field (a 1)*y

 theorem line_Z_factor (a : Fin 3 → K) : lineDifferential a=ZEquation a • omega :=
  actual_global_line_germ a

 theorem YEquation_times_y (a : Fin 3 → K) : YEquation a*y=ZEquation a := by
  unfold YEquation ZEquation
  rw [YZ_transition.1,YZ_transition.2]
  field_simp [ThetaActualLineDifferentials.y_ne_zero]
  ring

 theorem line_Y_factor (a : Fin 3 → K) : lineDifferential a=YEquation a • (y • omega) := by
  rw [line_Z_factor,smul_smul,YEquation_times_y]

/-- Every actual regular differential is the TRUE generic germ of an actual
canonical-plane section, retaining the natural global-to-field diagram. -/
theorem regular_is_line {η : Ω[field⁄K]} (hη : η∈regularDifferentials K field) :
    ∃a : Fin 3 → K,lineDifferential a=η := by
  let r : regularDifferentials K field := ⟨η,hη⟩
  let s : Γ(toBase.kaehler,⊤) := globalRegularEquiv.symm r
  let l := planeGlobalSectionEquiv.symm s
  let a := (dotProductEquiv K (Fin 3)).symm l
  refine ⟨a,?_⟩
  have hs : lineSection a=s := by
    simp only [lineSection,a,l,LinearEquiv.apply_symm_apply]
  rw [lineDifferential,hs,←globalRegularEquiv_germ]
  exact congrArg Subtype.val (globalRegularEquiv.apply_symm_apply r)

/-- At a genuine Y-chart point, whenever yomega is the actual local
canonical unit (derived below for our contact pairs), positive canonical
order is EQUIVALENT to the original native plane linear form vanishing.
Z=0 is allowed; no infinity point is removed. -/
theorem Y_positive_iff_value_zero (vals : Fin 2 → K)
    (hv : ∀i : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation 1 i)=0)
    (a : Fin 3 → K) (hη : lineDifferential a≠0)
    (hframe : (rationalPlace 1 vals hv).val.ordDifferential (y • omega)=0) :
    0<(rationalPlace 1 vals hv).val.ordDifferential (lineDifferential a) ↔
      a 0*vals 0+a 1+a 2*vals 1=0 := by
  let p := rationalPlace 1 vals hv
  let w := p.val
  let A := w.toValuationSubring
  let e : A →ₐ[K] K := evaluate w p.property
  let U : A := coordinateValue 1 vals hv 0
  let V : A := coordinateValue 1 vals hv 1
  let f : A := algebraMap K A (a 0)*U+algebraMap K A (a 1)+algebraMap K A (a 2)*V
  have hU : (U:field)=uY := coordinateValue_coe 1 vals hv 0
  have hV : (V:field)=vY := coordinateValue_coe 1 vals hv 1
  have hf : (f:field)=YEquation a := by
    change ((algebraMap K A (a 0):A):field)*(U:field)+((algebraMap K A (a 1):A):field)+
      ((algebraMap K A (a 2):A):field)*(V:field)=_
    rw [hU,hV,Place.coe_algebraMap,Place.coe_algebraMap,Place.coe_algebraMap]
    rfl
  have hfn : (f:field)≠0 := by
    intro hz
    apply hη
    rw [line_Y_factor,←hf,hz,zero_smul]
  have hn : f≠0 := by intro hz;exact hfn (congrArg Subtype.val hz)
  have he : e f=a 0*vals 0+a 1+a 2*vals 1 := by
    have h0 : e U=vals 0 := evaluate_coordinateValue 1 vals hv 0
    have h1 : e V=vals 1 := evaluate_coordinateValue 1 vals hv 1
    have hc (i : Fin 3) : e (algebraMap K A (a i))=a i := e.commutes (a i)
    simp only [f,map_add,map_mul,h0,h1,hc]
  have hb : y • omega≠0 := smul_ne_zero ThetaActualLineDifferentials.y_ne_zero omega_ne_zero
  have ho : w.ordDifferential (lineDifferential a)=w.ord (f:field) := by
    rw [line_Y_factor,w.ordDifferential_smul (by rw [←hf];exact hfn) (coefficient_ne_zero hb w)]
    rw [←hf]
    change w.ord (f:field)+w.ordDifferential (y • omega)=w.ord (f:field)
    rw [hframe,add_zero]
  change 0<w.ordDifferential (lineDifferential a) ↔ _
  rw [ho]
  constructor
  · intro hp
    have hm := (Place.mem_maximalIdeal_iff_ord_pos' hn).mpr hp
    rw [←localEval_kernel e] at hm
    change e f=0 at hm
    exact he.symm.trans hm
  · intro hz
    have hm : f∈IsLocalRing.maximalIdeal A := by
      rw [←localEval_kernel e]
      change e f=0
      exact he.trans hz
    exact (Place.mem_maximalIdeal_iff_ord_pos' hn).mp hm

 theorem Z_positive_iff_value_zero (vals : Fin 2 → K)
    (hv : ∀i : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation 2 i)=0)
    (a : Fin 3 → K) (hη : lineDifferential a≠0)
    (hframe : (rationalPlace 2 vals hv).val.ordDifferential omega=0) :
    0<(rationalPlace 2 vals hv).val.ordDifferential (lineDifferential a) ↔
      a 0*vals 0+a 1*vals 1+a 2=0 := by
  let p := rationalPlace 2 vals hv
  let w := p.val
  let A := w.toValuationSubring
  let e : A →ₐ[K] K := evaluate w p.property
  let U : A := coordinateValue 2 vals hv 0
  let V : A := coordinateValue 2 vals hv 1
  let f : A := algebraMap K A (a 0)*U+algebraMap K A (a 1)*V+algebraMap K A (a 2)
  have hU : (U:field)=x := coordinateValue_coe 2 vals hv 0
  have hV : (V:field)=y := coordinateValue_coe 2 vals hv 1
  have hf : (f:field)=ZEquation a := by
    change ((algebraMap K A (a 0):A):field)*(U:field)+((algebraMap K A (a 1):A):field)*(V:field)+
      ((algebraMap K A (a 2):A):field)=_
    rw [hU,hV,Place.coe_algebraMap,Place.coe_algebraMap,Place.coe_algebraMap]
    unfold ZEquation
    ring
  have hfn : (f:field)≠0 := by
    intro hz
    apply hη
    rw [line_Z_factor,←hf,hz,zero_smul]
  have hn : f≠0 := by intro hz;exact hfn (congrArg Subtype.val hz)
  have he : e f=a 0*vals 0+a 1*vals 1+a 2 := by
    have h0 : e U=vals 0 := evaluate_coordinateValue 2 vals hv 0
    have h1 : e V=vals 1 := evaluate_coordinateValue 2 vals hv 1
    have hc (i : Fin 3) : e (algebraMap K A (a i))=a i := e.commutes (a i)
    simp only [f,map_add,map_mul,h0,h1,hc]
  have ho : w.ordDifferential (lineDifferential a)=w.ord (f:field) := by
    rw [line_Z_factor,w.ordDifferential_smul (by rw [←hf];exact hfn) (coefficient_ne_zero omega_ne_zero w)]
    rw [←hf]
    change w.ord (f:field)+w.ordDifferential omega=w.ord (f:field)
    rw [hframe,add_zero]
  change 0<w.ordDifferential (lineDifferential a) ↔ _
  rw [ho]
  constructor
  · intro hp
    have hm := (Place.mem_maximalIdeal_iff_ord_pos' hn).mpr hp
    rw [←localEval_kernel e] at hm
    change e f=0 at hm
    exact he.symm.trans hm
  · intro hz
    have hm : f∈IsLocalRing.maximalIdeal A := by
      rw [←localEval_kernel e]
      change e f=0
      exact he.trans hz
    exact (Place.mem_maximalIdeal_iff_ord_pos' hn).mp hm

#print axioms regular_is_line
#print axioms Y_positive_iff_value_zero
#print axioms Z_positive_iff_value_zero
end
end FourCorner.ThetaCanonicalLinePointValues
