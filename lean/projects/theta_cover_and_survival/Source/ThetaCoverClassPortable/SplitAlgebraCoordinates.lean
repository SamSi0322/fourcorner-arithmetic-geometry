import ThetaCoverClassPortable.FiniteMapEtaleBridge
import Mathlib.Algebra.Algebra.Pi
set_option autoImplicit false
noncomputable section
universe u
open scoped TensorProduct
namespace FourCorner.SplitAlgebraCoordinates
variable (F : Type u) [CommRing F]
  (R B : Type u) [CommRing R] [CommRing B] [Algebra F R] [Algebra F B]
  (m : ℕ) (φ : (R ⊗[F] B) ≃ₐ[R] (Fin m → R))

def tensorCoordinate (j : Fin m) : R ⊗[F] B →ₐ[R] R :=
  (Pi.evalAlgHom R (fun _ : Fin m => R) j).comp φ.toAlgHom

def coordinate (j : Fin m) : B →ₐ[F] R :=
  ((tensorCoordinate F R B m φ j).restrictScalars F).comp Algebra.TensorProduct.includeRight

lemma tensorCoordinate_tmul (j : Fin m) (r : R) (b : B) :
    tensorCoordinate F R B m φ j (r ⊗ₜ[F] b) = r * coordinate F R B m φ j b := by
  rw [show r ⊗ₜ[F] b = r • ((1 : R) ⊗ₜ[F] b) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  rw [map_smul]
  rfl

/-- The coordinates remain distinct after EVERY ring map from R to a field. -/
theorem coordinate_injective_after_field (k : Type u) [Field k] (τ : R →+* k) :
    Function.Injective (fun j => τ.comp (coordinate F R B m φ j).toRingHom) := by
  classical
  intro j j' h
  by_contra hne
  have hB : ∀ b : B, τ (coordinate F R B m φ j b) = τ (coordinate F R B m φ j' b) :=
    fun b => congrArg (fun f : B →+* k => f b) h
  have hT : ∀ t : R ⊗[F] B,
      τ (tensorCoordinate F R B m φ j t) = τ (tensorCoordinate F R B m φ j' t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r b => simp only [tensorCoordinate_tmul, map_mul, hB]
  let v : Fin m → R := fun a => if a = j then 1 else 0
  have ht := hT (φ.symm v)
  have hj : v j = 1 := by simp [v]
  have hj' : v j' = 0 := by simp [v, Ne.symm hne]
  change τ (φ (φ.symm v) j) = τ (φ (φ.symm v) j') at ht
  rw [φ.apply_symm_apply, hj, hj', map_one, map_zero] at ht
  exact one_ne_zero ht

end FourCorner.SplitAlgebraCoordinates
