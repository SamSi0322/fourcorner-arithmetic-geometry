import ThetaLocalSurvivalPortable.SquareZeroKernelDivision

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj FourCorner.ThetaLocalSurvival.SquareZeroScalars
namespace FourCorner.ThetaLocalSurvival.Infinitesimal
open Multiplication
variable (G : Over base) [GrpObj G] [IsCommMonObj G]
variable (R : Type) [CommRing R] [Algebra ℚ R] (I : Ideal R) (hI : I^2=⊥)
variable (m : ℕ) (hm : 0<m)

include hI hm in
/-- Actual group powers are injective on each infinitesimal reduction
fibre, proved from the genuine square-zero kernel calculation. -/
theorem power_injective_on_reduction_fibre (P Q : points G R)
    (hred : idealReduction G R I P=idealReduction G R I Q) (hpow : P^m=Q^m) : P=Q := by
  let D : idealKernel G R I := ⟨P*Q⁻¹,by
    change idealReduction G R I (P*Q⁻¹)=1
    rw [map_mul,map_inv,hred,mul_inv_cancel]⟩
  have hD : D^m=(1 : idealKernel G R I) := by
    apply Subtype.ext
    change (P*Q⁻¹)^m=1
    rw [mul_pow,inv_pow,hpow,mul_inv_cancel]
  have hd : D=1 := (actual_square_zero_kernel_pow_injective G R I hI m hm) (by simpa only [one_pow] using hD)
  have hh := congrArg Subtype.val hd
  change P*Q⁻¹=1 at hh
  exact mul_inv_eq_one.mp hh

include hI hm in
/-- Given an actual smooth lift, correction by a unique actual kernel
root solves the multiplication lifting diagram. No lifting conclusion
or etaleness is assumed as input. -/
theorem correct_square_zero_lift (P0 : points G (R⧸I)) (H L : points G R)
    (hL : idealReduction G R I L=P0) (hH : idealReduction G R I H=P0^m) :
    ∃! P : points G R,idealReduction G R I P=P0 ∧ P^m=H := by
  let K : idealKernel G R I := ⟨H*(L^m)⁻¹,by
    change idealReduction G R I (H*(L^m)⁻¹)=1
    rw [map_mul,map_inv,map_pow,hH,hL,mul_inv_cancel]⟩
  obtain ⟨k,hk,_⟩ := actual_square_zero_kernel_unique_root G R I hI m hm K
  let P : points G R := L*k.val
  have hred : idealReduction G R I P=P0 := by
    change idealReduction G R I (L*k.val)=P0
    rw [map_mul,hL,show idealReduction G R I k.val=1 from k.property,mul_one]
  have hpow : P^m=H := by
    have hkp := congrArg Subtype.val hk
    change k.val^m=H*(L^m)⁻¹ at hkp
    change (L*k.val)^m=H
    rw [mul_pow,hkp]
    calc
      L^m*(H*(L^m)⁻¹)=H*(L^m*(L^m)⁻¹) := by ac_rfl
      _=H := by rw [mul_inv_cancel,mul_one]
  refine ⟨P,⟨hred,hpow⟩,?_⟩
  intro Q hQ
  exact power_injective_on_reduction_fibre G R I hI m hm Q P
    (hQ.1.trans hred.symm) (hQ.2.trans hpow.symm)

end FourCorner.ThetaLocalSurvival.Infinitesimal
