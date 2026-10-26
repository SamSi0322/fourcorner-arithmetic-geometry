import geometry.MultiquadraticTower
import Mathlib.RingTheory.PowerBasis

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace FourCorner.CriticalQuadraticLift
open Polynomial IntermediateField
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
local instance firstAlgebra (a : F) : Algebra F (Multiquadratic.Tower.first F a) := (Multiquadratic.Tower.first F a).toSubalgebra.algebra
local instance firstModule (a : F) : Module F (Multiquadratic.Tower.first F a) := (firstAlgebra a).toModule

def lift (a : F) (ha : ¬IsSquare a) (r : E) (hr : r^2=algebraMap F E a) :
    Multiquadratic.Tower.first F a →ₐ[F] E := by
  let pb:=IntermediateField.adjoin.powerBasis (Multiquadratic.radical_integral F a)
  have he : aeval (Multiquadratic.radical F a) (X^2-C a : F[X])=0 := by
    simp [Multiquadratic.radical_sq]
  have hir : Irreducible (X^2-C a : F[X]) :=
    (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr (by
      intro u hu
      apply ha
      exact ⟨u,by simpa only [pow_two] using hu.symm⟩)
  have hm : minpoly F pb.gen=X^2-C a := by
    rw [IntermediateField.adjoin.powerBasis_gen,minpoly_gen]
    exact (minpoly.eq_of_irreducible_of_monic hir he (monic_X_pow_sub_C a (by decide))).symm
  exact pb.lift r (by rw [hm];simpa only [map_sub,map_pow,aeval_X,aeval_C,sub_eq_zero] using hr)

@[simp] theorem lift_root (a : F) (ha : ¬IsSquare a) (r : E) (hr : r^2=algebraMap F E a) :
    lift a ha r hr (Multiquadratic.Tower.stepRoot₁ F a)=r := by
  unfold lift
  exact PowerBasis.lift_gen (IntermediateField.adjoin.powerBasis (Multiquadratic.radical_integral F a)) r _

end FourCorner.CriticalQuadraticLift
#print axioms FourCorner.CriticalQuadraticLift.lift
#print axioms FourCorner.CriticalQuadraticLift.lift_root
