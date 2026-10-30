import ThetaCoverClassPortable.ThetaQuadraticKernel
import Mathlib.RingTheory.RingHom.Etale
noncomputable section
namespace FourCorner.ThetaPairPresentation
open Algebra AlgebraicGeometry
universe u
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
/-- Genuine algebraic presentation data for a pair of roots; all fields will be
constructed for the literal source charts and their actual base changes. -/
structure Data where
  a : R
  b : R
  c : R
  u : S
  v : S
  base_conic : a*b=c^2
  u_sq : u^2=algebraMap R S a
  v_sq : v^2=algebraMap R S b
  uv : u*v=algebraMap R S c
  lift : ∀ {T : Type u} [CommRing T] [Algebra R T] (x y : T),
    x^2=algebraMap R T a → y^2=algebraMap R T b → x*y=algebraMap R T c → S →ₐ[R] T
  lift_u : ∀ {T : Type u} [CommRing T] [Algebra R T] (x y : T) (hx) (hy) (hc),
    lift x y hx hy hc u=x
  lift_v : ∀ {T : Type u} [CommRing T] [Algebra R T] (x y : T) (hx) (hy) (hc),
    lift x y hx hy hc v=y
  hom_ext : ∀ {T : Type u} [CommRing T] [Algebra R T] {f g : S →ₐ[R] T},
    f u=g u → f v=g v → f=g
variable {R S}
variable (P : Data R S)
abbrev Q := ThetaQuadraticKernel.Q P.b
abbrev r : Q P := ThetaQuadraticKernel.root P.b
lemma r_unit (hb : IsUnit P.b) : IsUnit (r P) := ThetaQuadraticKernel.root_unit P.b hb
def complementary (hb : IsUnit P.b) : Q P := algebraMap R (Q P) P.c*↑(r_unit P hb).unit⁻¹
lemma complementary_mul (hb : IsUnit P.b) : complementary P hb*r P=algebraMap R (Q P) P.c := by
  rw [complementary,mul_assoc,(r_unit P hb).val_inv_mul,mul_one]
lemma complementary_sq (hb : IsUnit P.b) : complementary P hb^2=algebraMap R (Q P) P.a := by
  apply ((r_unit P hb).pow 2).mul_left_cancel
  calc
    r P^2*complementary P hb^2=(complementary P hb*r P)^2 := by ring
    _=(algebraMap R (Q P) P.c)^2 := by rw [complementary_mul]
    _=algebraMap R (Q P) (P.a*P.b) := by simpa only [map_pow] using congrArg (algebraMap R (Q P)) P.base_conic.symm
    _=r P^2*algebraMap R (Q P) P.a := by rw [ThetaQuadraticKernel.root_sq,map_mul];ring

def toQuadratic (hb : IsUnit P.b) : S →ₐ[R] Q P :=
  P.lift (complementary P hb) (r P) (complementary_sq P hb) (ThetaQuadraticKernel.root_sq P.b) (complementary_mul P hb)
def fromQuadratic : Q P →ₐ[R] S := ThetaQuadraticKernel.ofRoot P.b P.v P.v_sq
@[simp] lemma fromQuadratic_root : fromQuadratic P (r P)=P.v := ThetaQuadraticKernel.ofRoot_root _ _ _
@[simp] lemma toQuadratic_u (hb : IsUnit P.b) : toQuadratic P hb P.u=complementary P hb := P.lift_u _ _ _ _ _
@[simp] lemma toQuadratic_v (hb : IsUnit P.b) : toQuadratic P hb P.v=r P := P.lift_v _ _ _ _ _
lemma fromQuadratic_complementary (hb : IsUnit P.b) :
    fromQuadratic P (complementary P hb)=P.u := by
  have hv : IsUnit P.v := by simpa only [fromQuadratic_root] using (r_unit P hb).map (fromQuadratic P)
  apply hv.mul_right_cancel
  calc
    fromQuadratic P (complementary P hb)*P.v=
        fromQuadratic P (complementary P hb*r P) := by rw [map_mul,fromQuadratic_root]
    _=algebraMap R S P.c := by rw [complementary_mul,AlgHom.commutes]
    _=P.u*P.v := P.uv.symm
/-- A unit square coefficient gives an actual quadratic-algebra isomorphism. -/
def equiv (hb : IsUnit P.b) : S ≃ₐ[R] Q P :=
  AlgEquiv.ofAlgHom (toQuadratic P hb) (fromQuadratic P)
    (by apply ThetaQuadraticKernel.hom_ext; simp)
    (by apply P.hom_ext <;> simp [fromQuadratic_complementary])
lemma finite (hb : IsUnit P.b) : Module.Finite R S := by
  haveI := ThetaQuadraticKernel.finite P.b
  exact Module.Finite.equiv (equiv P hb).symm.toLinearEquiv
lemma algebra_etale (hb : IsUnit P.b) (h2 : IsUnit (2:R)) : Algebra.Etale R S := by
  have he:=ThetaQuadraticKernel.etale P.b hb h2
  have hr : (algebraMap R (Q P)).Etale :=
    (HasRingHomProperty.Spec_iff (P:=@AlgebraicGeometry.Etale)).mp he
  haveI : Algebra.Etale R (Q P) := RingHom.etale_algebraMap.mp hr
  exact Algebra.Etale.of_equiv (equiv P hb).symm
end FourCorner.ThetaPairPresentation
#print axioms FourCorner.ThetaPairPresentation.equiv
#print axioms FourCorner.ThetaPairPresentation.finite
#print axioms FourCorner.ThetaPairPresentation.algebra_etale
