import CriticalEllipticField
import IntegralEvaluationInjection

noncomputable section
namespace FourCorner.CriticalEllipticEvaluation
open Polynomial CriticalEllipticField
variable (k : Type*) [Field k]
variable {L : Type*} [Field L] [Algebra k L]
set_option maxHeartbeats 1500000

/-- The native coordinate evaluator is injective when its actual X value
is transcendental. Integrality over k[X] proves injectivity, not an assumed
function-field identification. -/
theorem evaluate_injective (x y : L) (h : y^2=x^3-x) (hx : Transcendental k x) :
    Function.Injective (evaluate k x y h) := by
  letI : Module.Finite k[X] (ring k) :=
    Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis (curve k).toAffine)
  apply IntegralEvaluationInjection.injective_of_base (R := k[X]) (evaluate k x y h).toRingHom
  have he : (evaluate k x y h).toRingHom.comp (algebraMap k[X] (ring k)) =
      (Polynomial.aeval x).toRingHom := by
    apply RingHom.ext
    intro p
    change evaluate k x y h (AdjoinRoot.of ((curve k).toAffine.polynomial) p) = Polynomial.aeval x p
    dsimp only [evaluate]
    exact AdjoinRoot.liftAlgHom_of _ _ _ _ p
  rw [he]
  exact transcendental_iff_injective.mp hx

/-- A genuine field homomorphism out of the native Weierstrass function
field, constructed from the actual affine coordinates. -/
def embedding (x y : L) (h : y^2=x^3-x) (hx : Transcendental k x) :
    field k →ₐ[k] L :=
  IsFractionRing.liftAlgHom (evaluate_injective k x y h hx)

theorem embedding_ring (x y : L) (h : y^2=x^3-x) (hx : Transcendental k x) (a : ring k) :
    embedding k x y h hx (algebraMap (ring k) (field k) a)=evaluate k x y h a := by
  exact IsFractionRing.lift_algebraMap (evaluate_injective k x y h hx) a

@[simp] theorem embedding_x (x y : L) (h : y^2=x^3-x) (hx : Transcendental k x) :
    embedding k x y h hx (CriticalEllipticField.x k)=x := by
  rw [CriticalEllipticField.x,embedding_ring,evaluate_x]
@[simp] theorem embedding_y (x y : L) (h : y^2=x^3-x) (hx : Transcendental k x) :
    embedding k x y h hx (CriticalEllipticField.y k)=y := by
  rw [CriticalEllipticField.y,embedding_ring,evaluate_y]

end FourCorner.CriticalEllipticEvaluation
#print axioms FourCorner.CriticalEllipticEvaluation.evaluate_injective
#print axioms FourCorner.CriticalEllipticEvaluation.embedding_x
#print axioms FourCorner.CriticalEllipticEvaluation.embedding_y
