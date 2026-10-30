import ThetaCoverClassPortable.ThetaCoverFunctions
import ThetaCoverClassPortable.ThetaDCanonicalInfinityDivisor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaCoverPoleBound
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaCoverFunctions
open ThetaDActualDifferential ThetaRegularFunctionDifferential ThetaDPlaneRegularForms
open ThetaDGlobalCanonicalCandidate ThetaDCanonicalInfinityDivisor DivisorPicClassification
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : CharZero field := charZero_of_injective_algebraMap (algebraMap K field).injective
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

 theorem ord_numeral (w : Place K field) (n : ℕ) (hn : n≠0) : w.ord (n:field)=0 := by
  have hnK : (n:K)≠0 := Nat.cast_ne_zero.mpr hn
  simpa only [map_natCast] using (ord_base_constant w hnK)

 theorem ord_h (w : Place K field) : w.ord h=w.ord c0 := by
  have h2 : w.ord (2:field)=0 := by simpa only [Nat.cast_ofNat] using ord_numeral w 2 (by decide)
  unfold h
  rw [div_eq_mul_inv,w.ord_mul c0_ne_zero (inv_ne_zero (by norm_num)),w.ord_inv,
    h2]
  omega

/-- A bound at EVERY actual native Place, including ALL infinity places.
It comes from true x*omega/y*omega regularity, not a guessed pole set. -/
theorem conic_all_place_bound (w : Place K field) :
    -2*infinitySum w≤w.ord c0 := by
  let a : field := coefficient w omega
  have ha : a≠0 := coefficient_nonzero w
  let A := w.toValuationSubring
  have hA : a∈w.toValuationSubring := all_coefficients_regular w
  have hxA : x*a∈w.toValuationSubring := by
    simpa only [a,map_smul,smul_eq_mul] using xomega_coefficient_regular w
  have hyA : y*a∈w.toValuationSubring := by
    simpa only [a,map_smul,smul_eq_mul] using yomega_coefficient_regular w
  let av : A := ⟨a,hA⟩
  let xv : A := ⟨x*a,hxA⟩
  let yv : A := ⟨y*a,hyA⟩
  let cv : A := xv^2+yv^2-2*(av*av)
  have hcv : (cv:field)=c0*(a*a) := by
    change (x*a)^2+(y*a)^2-2*(a*a)=c0*(a*a)
    unfold c0
    ring
  have hcA : c0*(a*a)∈w.toValuationSubring := hcv ▸ cv.property
  have ho := w.ord_nonneg_of_mem hcA
  rw [w.ord_mul c0_ne_zero (mul_ne_zero ha ha),w.ord_mul ha ha] at ho
  have hH : w.ord a=infinitySum w := by
    change w.ordDifferential omega=infinitySum w
    rw [←canonicalDivisorOf_apply omega_ne_zero,canonical_divisor_exact]
  rw [hH] at ho
  omega

 theorem h_all_place_bound (w : Place K field) : -2*infinitySum w≤w.ord h := by
  rw [ord_h]
  exact conic_all_place_bound w

#print axioms conic_all_place_bound
end FourCorner.ThetaCoverPoleBound
