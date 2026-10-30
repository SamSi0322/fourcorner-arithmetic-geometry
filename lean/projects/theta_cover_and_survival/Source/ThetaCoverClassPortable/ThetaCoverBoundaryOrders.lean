import ThetaCoverClassPortable.ThetaCoverBoundaryPoints
import ThetaCoverClassPortable.ThetaCoverPoleBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.ThetaCoverBoundaryOrders
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaCoverFunctions
open ThetaCoverPoleBound ThetaCoverBoundaryPoints ThetaGeometricResidueCoordinates
open ThetaDCanonicalInfinityDivisor ResiduePlaceEvaluation SchemePointStalkEvaluation
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : CharZero field := charZero_of_injective_algebraMap (algebraMap K field).injective

/-- N genuinely vanishes in the actual residue field of each literal E;
1-x²/2 genuinely evaluates to 1/2 there and is therefore a DVR unit. -/
theorem boundary_conic_order (s : Signs) : 2≤(place s).ord c0 := by
  let w := place s
  let A := w.toValuationSubring
  let e : A →ₐ[K] K := evaluate w (rationalPlace 2 (values s) (relations s)).property
  let a : A := xValue s
  let b : A := yValue s
  have ha : (a:field)=x := xValue_coe s
  have hb : (b:field)=y := yValue_coe s
  have ea : e a=sign s.1 := xValue_eval s
  have eb : e b=sign s.2 := yValue_eval s
  let n : A := 97*a^2+99*b^2-196
  let q : A := 1-a^2*algebraMap K A ((2:K)⁻¹)
  have hn : (n:field)=numerator := by
    change 97*(a:field)^2+99*(b:field)^2-196=numerator
    rw [ha,hb]
    rfl
  have hq : (q:field)=1-x^2/2 := by
    change 1-(a:field)^2*((algebraMap K A ((2:K)⁻¹):A):field)=_
    rw [ha,Place.coe_algebraMap,map_inv₀,map_ofNat]
    rfl
  have en : e n=0 := by
    simp only [n,map_sub,map_add,map_mul,map_pow,map_ofNat,ea,eb,ThetaActualPoints.sign_sq]
    norm_num
  have eq : e q=(1/2:K) := by
    simp only [q,map_sub,map_mul,map_pow,map_one,ea,ThetaActualPoints.sign_sq,
      one_mul,AlgHom.commutes]
    norm_num
  have hnu : n∈IsLocalRing.maximalIdeal A := by
    rw [←localEval_kernel e]
    exact en
  have hqu : IsUnit q := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hh
    rw [←localEval_kernel e] at hh
    have hz : e q=0 := hh
    rw [eq] at hz
    norm_num at hz
  have hn0 : n≠0 := by
    intro hz
    exact numerator_ne_zero (hn.symm.trans (congrArg Subtype.val hz))
  have hnord : 0<w.ord numerator := by
    have hh := (Place.mem_maximalIdeal_iff_ord_pos' hn0).mp hnu
    change 0<w.ord (n:field) at hh
    rwa [hn] at hh
  have hqord : w.ord (1-x^2/2)=0 := by
    have hh := w.ord_coe_unit hqu.unit
    have he : ((hqu.unit:A):field)=(q:field) := congrArg (fun z:A=>(z:field)) hqu.unit_spec
    rw [he,hq] at hh
    exact hh
  have hq0 : 1-x^2/2≠0 := by
    intro hz
    have hh : q=0 := Subtype.ext (hq.trans hz)
    exact hqu.ne_zero hh
  have h784 : w.ord (784:field)=0 := by simpa only [Nat.cast_ofNat] using ord_numeral w 784 (by decide)
  have he := congrArg w.ord conic_identity
  rw [pow_two,w.ord_mul numerator_ne_zero numerator_ne_zero,
    w.ord_mul (mul_ne_zero (by norm_num) c0_ne_zero) hq0,
    w.ord_mul (by norm_num) c0_ne_zero,h784,hqord] at he
  change 2≤w.ord c0
  omega

 theorem boundary_h_order (s : Signs) : 2≤(place s).ord h := by
  rw [ord_h]
  exact boundary_conic_order s

#print axioms boundary_conic_order
end FourCorner.ThetaCoverBoundaryOrders
