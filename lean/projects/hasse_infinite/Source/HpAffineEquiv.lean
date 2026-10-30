import HpAffineInverse
import HpPolynomialFractionField

namespace FourCorner.HpAffineEquiv
open Polynomial MvPolynomial HpAffineUniversal HpAffineInverse
noncomputable section
variable (K : Type*) [Field K] [CharZero K]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

theorem fromUniversal_coeff (p : K) (hp : p ≠ 0) (c : K) :
    fromUniversal K p hp (coeff K p c)=algebraMap K (B K p) c := by
  change fromUniversal K p hp (algebraMap K[X] (A K p) (Polynomial.C c))=_
  rw [fromUniversal_base]
  exact Polynomial.eval₂_C _ _

theorem toUniversal_rho (p : K) (hp : p ≠ 0) :
    toUniversal K p (rhoB K p)=rhoA K p := by
  rw [rhoB,map_mul,map_pow,toUniversal_C,toUniversal_X,rootA_sq]
  change coeff K p p⁻¹*(coeff K p p*rhoA K p)=rhoA K p
  rw [← mul_assoc,← map_mul,inv_mul_cancel₀ hp,map_one,one_mul]

theorem toUniversal_base (p : K) (hp : p ≠ 0) :
    (toUniversal K p).comp (base K p)=algebraMap K[X] (A K p) := by
  apply Polynomial.ringHom_ext
  · intro c
    simpa only [RingHom.comp_apply,base,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,HpAffineUniversal.coeff] using toUniversal_C K p c
  · simpa only [RingHom.comp_apply,base,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,rhoA] using toUniversal_rho K p hp

theorem from_to (p : K) (hp : p ≠ 0) :
    (fromUniversal K p hp).comp (toUniversal K p)=RingHom.id (B K p) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    change fromUniversal K p hp (toUniversal K p (algebraMap K (B K p) c))=algebraMap K (B K p) c
    rw [toUniversal_C,fromUniversal_coeff]
  · intro i
    change fromUniversal K p hp (toUniversal K p (Ideal.Quotient.mk _ (MvPolynomial.X i)))=x K p i
    rw [toUniversal_X,fromUniversal_coord]

theorem to_from (p : K) (hp : p ≠ 0) :
    (toUniversal K p).comp (fromUniversal K p hp)=RingHom.id (A K p) := by
  apply HpFourRootUniversal.ringHom_ext K[X] (HpLiteralField.poly K p)
  · intro q
    change toUniversal K p (fromUniversal K p hp (algebraMap K[X] (A K p) q))=algebraMap K[X] (A K p) q
    rw [fromUniversal_base]
    exact RingHom.congr_fun (toUniversal_base K p hp) q
  · intro i
    change toUniversal K p (fromUniversal K p hp (rootA K p i))=rootA K p i
    rw [fromUniversal_coord]
    exact toUniversal_X K p i

/-- Exact ring isomorphism of the literal affine Z=1 chart of C_p with
the integral universal four-root algebra over K[rho]. Its inverse uses the
original rho=U²/p; every ordered coordinate is preserved. -/
def ringEquiv (p : K) (hp : p ≠ 0) : B K p ≃+* A K p where
  __ := toUniversal K p
  invFun := fromUniversal K p hp
  left_inv b := RingHom.congr_fun (from_to K p hp) b
  right_inv a := RingHom.congr_fun (to_from K p hp) a

 theorem affine_isDomain (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) : IsDomain (B K p) := by
  letI := HpPolynomialRootAlgebra.isDomain K p hp ha hb
  exact Function.Injective.isDomain (ringEquiv K p hp) (ringEquiv K p hp).injective

#print axioms ringEquiv
#print axioms affine_isDomain
end
end FourCorner.HpAffineEquiv
