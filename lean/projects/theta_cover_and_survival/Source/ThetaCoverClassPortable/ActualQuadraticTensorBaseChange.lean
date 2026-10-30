import ThetaCoverClassPortable.ThetaQuadraticGeometricContacts
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct

namespace FourCorner.ActualQuadraticTensorBaseChange
variable {R S : Type} [Field R] [Field S] [Algebra R S] (a b : R)

/-- Coefficient extension of the ACTUAL quadratic algebra. -/
def coefficientMap : QuadraticAlgebra R a b →ₐ[R]
    QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b) where
  toFun z := ⟨algebraMap R S z.re,algebraMap R S z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' z w := by apply QuadraticAlgebra.ext <;> simp
  map_mul' z w := by apply QuadraticAlgebra.ext <;> simp
  commutes' r := by
    change (⟨algebraMap R S r,algebraMap R S 0⟩ :
      QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) = ⟨algebraMap R S r,0⟩
    rw [map_zero]

def forward : S ⊗[R] QuadraticAlgebra R a b →ₐ[S]
    QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b) :=
  { (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R S (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)))
      (coefficientMap a b) (fun _ _ => Commute.all _ _)).toRingHom with
    commutes' := by intro s;simp [Algebra.TensorProduct.algebraMap_apply,Algebra.TensorProduct.lift_tmul] }

theorem forward_tmul (s : S) (z : QuadraticAlgebra R a b) :
    forward a b (s ⊗ₜ[R] z) =
      (⟨s*algebraMap R S z.re,s*algebraMap R S z.im⟩ :
        QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) := by
  apply QuadraticAlgebra.ext <;>
    simp [forward,Algebra.TensorProduct.lift_tmul,coefficientMap,QuadraticAlgebra.algebraMap_eq]

theorem forward_surjective : Function.Surjective (forward (S:=S) a b) := by
  rintro ⟨x,y⟩
  refine ⟨x ⊗ₜ[R] (1 : QuadraticAlgebra R a b)+
    y ⊗ₜ[R] (QuadraticAlgebra.omega : QuadraticAlgebra R a b),?_⟩
  rw [map_add,forward_tmul,forward_tmul]
  apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

/-- Genuine tensor base-change isomorphism, retaining the two coefficients
and the actual tensor generators. No splitting or root hypothesis is used. -/
def equivalence : (S ⊗[R] QuadraticAlgebra R a b) ≃ₐ[S]
    QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b) := by
  have hd : Module.finrank S (S ⊗[R] QuadraticAlgebra R a b)=
      Module.finrank S (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) := by
    rw [Module.finrank_eq_card_basis ((QuadraticAlgebra.basis a b).baseChange S),
      Module.finrank_eq_card_basis (QuadraticAlgebra.basis (algebraMap R S a) (algebraMap R S b))]
  exact AlgEquiv.ofBijective (forward a b)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (forward a b).toLinearMap) hd).mpr (forward_surjective a b),
      forward_surjective a b⟩

theorem equivalence_tmul (s : S) (z : QuadraticAlgebra R a b) :
    equivalence a b (s ⊗ₜ[R] z) =
      (⟨s*algebraMap R S z.re,s*algebraMap R S z.im⟩ :
        QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) :=
  forward_tmul a b s z

end FourCorner.ActualQuadraticTensorBaseChange
