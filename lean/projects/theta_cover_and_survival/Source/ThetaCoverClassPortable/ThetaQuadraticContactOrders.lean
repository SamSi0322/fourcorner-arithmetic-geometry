import ThetaCoverClassPortable.ThetaQuadraticContactCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaQuadraticContactOrders
open ThetaQuadraticCurve ThetaQuadraticField ThetaQuadraticContactAlgebra ThetaQuadraticContactPlaces
open ThetaQuadraticContactCoordinates
local instance : IsIntegral curve := curve_integral
local instance : Algebra F functionField := fieldAlgebra
local instance : CharZero functionField := charZero_of_injective_algebraMap (algebraMap F functionField).injective

def ell (b : Bool) : functionField := if b then ellPlus2 else ellMinus2
theorem ell_ne_zero (b : Bool) : ell b≠0 := by
  cases b <;> simp [ell,ellPlus2_ne_zero,ellMinus2_ne_zero]

theorem polynomial_relation :
    9801*x2^4+19598*x2^2*y2^2-39592*x2^2+9801*y2^4-39592*y2^2+39984=0 := by
  apply toGeometric_injective
  simpa only [map_sub,map_add,map_mul,map_pow,map_ofNat,map_zero,coordinate_image]
    using ThetaDFieldCoordinates.polynomial_relation

theorem line_product : ellPlus2*ellMinus2=1-x2^2/2 := by
  unfold ellPlus2 ellMinus2
  field_simp [r2_ne_zero]
  ring_nf
  rw [r2_sq]
  ring

theorem tangent_square_identity :
    (99*y2^2-2)^2=(2-x2^2)*(9801*x2^2+19598*y2^2-19990) := by
  linear_combination polynomial_relation

theorem contact_line_order (b : Bool) : 2≤(contactPlace b).ord (ell b) := by
  let w := contactPlace b
  let A := w.toValuationSubring
  let e := valuationEvaluation b
  let a : A := coordinateValue b 0
  let c : A := coordinateValue b 1
  let rr : A := algebraMap F A QuadraticAlgebra.omega
  let ri : A := algebraMap F A (QuadraticAlgebra.omega⁻¹)
  have ha : (a:functionField)=x2 := coordinateValue_coe b 0
  have hc : (c:functionField)=y2 := coordinateValue_coe b 1
  have er : e rr=radical := e.commutes _
  have eri : e ri=radical⁻¹ := by
    rw [show e ri=algebraMap F contactField (QuadraticAlgebra.omega⁻¹) from e.commutes _]
    exact map_inv₀ _ _
  have ea : e a=abscissa b := coordinateValue_eval b 0
  have ec : e c=ordinate := coordinateValue_eval b 1
  let t : A := 99*c^2-2
  let d : A := 9801*a^2+19598*c^2-19990
  let q : A := if b then 1-a*ri else 1+a*ri
  have et : e t=0 := by
    simp only [t,map_sub,map_mul,map_pow,map_ofNat,ec,ordinate_sq]
    norm_num
  have ed : e d=(784/99:contactField) := by
    simp only [d,map_sub,map_add,map_mul,map_pow,map_ofNat,ea,ec,ordinate_sq,abscissa_sq]
    norm_num
  have hrn : radical≠0 := by
    intro hz
    have h := radical_sq
    rw [hz,zero_pow (by decide)] at h
    norm_num at h
  have eq : e q=2 := by
    cases b <;> simp only [q,Bool.false_eq_true,if_false,if_true,map_add,map_sub,map_one,map_mul,ea,eri,abscissa,neg_mul]
    all_goals rw [mul_inv_cancel₀ hrn];norm_num
  have hdu : IsUnit d := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro h
    rw [←valuationEvaluation_kernel b] at h
    have hz : e d=0 := h
    rw [ed] at hz
    norm_num at hz
  have hqu : IsUnit q := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro h
    rw [←valuationEvaluation_kernel b] at h
    have hz : e q=0 := h
    rw [eq] at hz
    norm_num at hz
  have ht : (t:functionField)=99*y2^2-2 := by
    change 99*(c:functionField)^2-2=_
    rw [hc]
  have hd : (d:functionField)=9801*x2^2+19598*y2^2-19990 := by
    change 9801*(a:functionField)^2+19598*(c:functionField)^2-19990=_
    rw [ha,hc]
  have hq : (q:functionField)=ell (!b) := by
    have hri : (ri:functionField)=r2⁻¹ := by
      change algebraMap F functionField (QuadraticAlgebra.omega⁻¹)=_
      exact map_inv₀ _ _
    cases b <;> simp only [q,ell,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,
      ellPlus2,ellMinus2,div_eq_mul_inv]
    · change 1+(a:functionField)*(ri:functionField)=1+x2*r2⁻¹
      rw [ha,hri]
    · change 1-(a:functionField)*(ri:functionField)=1-x2*r2⁻¹
      rw [ha,hri]
  have hdz : (d:functionField)≠0 := by
    intro h
    exact hdu.ne_zero (Subtype.ext h)
  have hprod : 2-x2^2≠0 := by
    have hp := mul_ne_zero ellPlus2_ne_zero ellMinus2_ne_zero
    rw [line_product] at hp
    intro hz
    apply hp
    linear_combination (1/2)*hz
  have htn : t≠0 := by
    intro hz
    have hh := tangent_square_identity
    rw [←ht,hz,ZeroMemClass.coe_zero,zero_pow (by decide),←hd] at hh
    exact (mul_ne_zero hprod hdz) hh.symm
  have htm : t∈IsLocalRing.maximalIdeal A := by
    rw [←valuationEvaluation_kernel b]
    exact et
  have hto : 0<w.ord (99*y2^2-2) := by
    have h := (Place.mem_maximalIdeal_iff_ord_pos' htn).mp htm
    change 0<w.ord (t:functionField) at h
    rwa [ht] at h
  have hdo : w.ord (9801*x2^2+19598*y2^2-19990)=0 := by
    have h := w.ord_coe_unit hdu.unit
    have he := congrArg (fun z:A => (z:functionField)) hdu.unit_spec
    rw [he,hd] at h
    exact h
  have hqo : w.ord (ell (!b))=0 := by
    have h := w.ord_coe_unit hqu.unit
    have he := congrArg (fun z:A => (z:functionField)) hqu.unit_spec
    rw [he,hq] at h
    exact h
  have h2 : w.ord (2:functionField)=0 := by
    simpa only [map_ofNat] using DivisorPicClassification.ord_base_constant w (by norm_num : (2:F)≠0)
  have he := tangent_square_identity
  have hlin : 2-x2^2=2*(ell b*ell (!b)) := by
    have hp := line_product
    cases b <;> simp only [ell,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true]
    all_goals linear_combination -2*hp
  rw [hlin] at he
  have hdz' : 9801*x2^2+19598*y2^2-19990≠0 := by rwa [hd] at hdz
  have htz : 99*y2^2-2≠0 := by intro hz;exact htn (Subtype.ext (ht.trans hz))
  have ho := congrArg w.ord he
  rw [pow_two,w.ord_mul htz htz,
    w.ord_mul (mul_ne_zero (by norm_num) (mul_ne_zero (ell_ne_zero b) (ell_ne_zero (!b)))) hdz',
    w.ord_mul (by norm_num) (mul_ne_zero (ell_ne_zero b) (ell_ne_zero (!b))),
    w.ord_mul (ell_ne_zero b) (ell_ne_zero (!b)),h2,hdo,hqo] at ho
  change 2≤w.ord (ell b)
  omega

end FourCorner.ThetaQuadraticContactOrders
