import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

noncomputable section
namespace FourCorner.CriticalEllipticField
open Polynomial
variable (k : Type*) [Field k]

def curve : WeierstrassCurve k := ⟨0,0,0,-1,0⟩
abbrev ring := (curve k).toAffine.CoordinateRing
abbrev field := (curve k).toAffine.FunctionField

def xRing : ring k := algebraMap k[X] (ring k) X
def yRing : ring k := AdjoinRoot.root (curve k).toAffine.polynomial
def x : field k := algebraMap (ring k) (field k) (xRing k)
def y : field k := algebraMap (ring k) (field k) (yRing k)

theorem ring_equation : yRing k ^2=xRing k ^3-xRing k := by
  have h := (AdjoinRoot.mk_self (f := (curve k).toAffine.polynomial))
  change (AdjoinRoot.mk ((curve k).toAffine.polynomial))
    (X^2+C (C 0*X+C 0)*X-C (X^3+C 0*X^2+C (-1)*X+C 0))=0 at h
  simp only [C_0,C_neg,C_1,zero_mul,zero_add,add_zero,map_sub,map_pow,
    AdjoinRoot.mk_X,AdjoinRoot.mk_C,map_add,map_mul,map_neg,map_one] at h
  change yRing k^2-(xRing k^3+-1*xRing k)=0 at h
  linear_combination h

theorem equation : y k ^2=x k ^3-x k := by
  simpa only [x,y,map_pow,map_sub] using congrArg (algebraMap (ring k) (field k)) (ring_equation k)

theorem x_transcendental : Transcendental k (x k) := by
  have hr : Transcendental k (xRing k) :=
    (transcendental_algebraMap_iff (R := k) (S := k[X])
      (FaithfulSMul.algebraMap_injective k[X] (ring k))).mpr (Polynomial.transcendental_X k)
  exact (transcendental_algebraMap_iff (R := k) (S := ring k)
    (IsFractionRing.injective (ring k) (field k))).mpr hr

/-- The genuine native affine coordinate ring evaluates at every literal
solution of y²=x³−x. This is not a map from an invented labelled field. -/
def evaluate {L : Type*} [Field L] [Algebra k L] (x y : L) (h : y^2=x^3-x) :
    ring k →ₐ[k] L :=
  AdjoinRoot.liftAlgHom ((curve k).toAffine.polynomial) (Polynomial.aeval x) y (by
    change Polynomial.eval₂ (Polynomial.aeval x).toRingHom y
      (X^2+C (C 0*X+C 0)*X-C (X^3+C 0*X^2+C (-1)*X+C 0))=0
    simp only [eval₂_sub,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
    simp [h,sub_eq_add_neg])

@[simp] theorem evaluate_x {L : Type*} [Field L] [Algebra k L] (x y : L) (h : y^2=x^3-x) :
    evaluate k x y h (xRing k)=x := by
  exact (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (Polynomial.aeval_X x)
@[simp] theorem evaluate_y {L : Type*} [Field L] [Algebra k L] (x y : L) (h : y^2=x^3-x) :
    evaluate k x y h (yRing k)=y := AdjoinRoot.liftAlgHom_root _ _ _ _

end FourCorner.CriticalEllipticField
#print axioms FourCorner.CriticalEllipticField.equation
#print axioms FourCorner.CriticalEllipticField.x_transcendental
#print axioms FourCorner.CriticalEllipticField.evaluate_x
#print axioms FourCorner.CriticalEllipticField.evaluate_y
