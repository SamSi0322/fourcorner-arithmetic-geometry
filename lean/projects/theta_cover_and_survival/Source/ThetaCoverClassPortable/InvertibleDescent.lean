import ThetaCoverClassPortable.FiniteProjectiveDescent
import Mathlib.RingTheory.PicardGroup

set_option autoImplicit false
open TensorProduct LinearMap
noncomputable section

namespace Module
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Dual base change for finite projective modules, constructed from tensor-Hom. -/
def finiteProjectiveDualBaseChange [Module.Finite R M] [Projective R M] :
    S ⊗[R] Dual R M ≃ₗ[S] Dual S (S ⊗[R] M) := by
  let e : S ⊗[R] Dual R M ≃ₗ[R] Dual S (S ⊗[R] M) :=
    TensorProduct.comm R S (Dual R M) ≪≫ₗ dualTensorHomEquiv R M S ≪≫ₗ
      (LinearMap.liftBaseChangeEquiv S).restrictScalars R
  apply LinearEquiv.ofBijective (show S ⊗[R] Dual R M →ₗ[S] Dual S (S ⊗[R] M) from
    { toFun := e
      map_add' := e.map_add
      map_smul' := ?_ }) e.bijective
  intro a x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul s f =>
    ext m
    change (dualTensorHom R M S (f ⊗ₜ[R] (a * s))).liftBaseChange S (1 ⊗ₜ m) =
      a * (dualTensorHom R M S (f ⊗ₜ[R] s)).liftBaseChange S (1 ⊗ₜ m)
    simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]

@[simp] theorem finiteProjectiveDualBaseChange_tmul [Module.Finite R M] [Projective R M]
    (s t : S) (f : Dual R M) (m : M) :
    finiteProjectiveDualBaseChange (s ⊗ₜ[R] f) (t ⊗ₜ[R] m) =
      s * t * algebraMap R S (f m) := by
  change (dualTensorHom R M S (f ⊗ₜ[R] s)).liftBaseChange S (t ⊗ₜ m) = _
  simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]

/-- Invertibility descends along faithfully flat scalar extension. The target
invertibility is proved by reflecting the actual dual evaluation isomorphism. -/
theorem Invertible.of_faithfullyFlat_tensorProduct [FaithfullyFlat R S]
    [Module.Invertible S (S ⊗[R] M)] : Module.Invertible R M := by
  letI : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  letI : Projective R M := Projective.of_faithfullyFlat_tensorProduct (S := S)
  let e : S ⊗[R] (Dual R M ⊗[R] M) ≃ₗ[S] S :=
    AlgebraTensorModule.distribBaseChange R S (Dual R M) M ≪≫ₗ
      (finiteProjectiveDualBaseChange (R := R) (S := S) (M := M)).rTensor (S ⊗[R] M) ≪≫ₗ
        Invertible.linearEquiv S (S ⊗[R] M)
  have he : (AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ
      (contractLeft R M).baseChange S = e.toLinearMap := by
    ext s f m
    simp [e, Invertible.linearEquiv, Algebra.smul_def, mul_comm]
  have hb : Function.Bijective ((contractLeft R M).baseChange S) := by
    have hh : (contractLeft R M).baseChange S =
        (AlgebraTensorModule.rid R S S).symm.toLinearMap ∘ₗ e.toLinearMap := by
      rw [← he]
      ext x
      simp
    rw [hh]
    exact (AlgebraTensorModule.rid R S S).symm.bijective.comp e.bijective
  exact ⟨(FaithfullyFlat.lTensor_bijective_iff_bijective R S (contractLeft R M)).mp hb⟩

/-- The concrete base-change equivalence supplied by effective descent suffices. -/
theorem Invertible.of_faithfullyFlat_equiv [FaithfullyFlat R S]
    {N : Type*} [AddCommGroup N] [Module S N] [Module.Invertible S N]
    (e : S ⊗[R] M ≃ₗ[S] N) : Module.Invertible R M := by
  letI : Module.Invertible S (S ⊗[R] M) := Invertible.congr e.symm
  exact Invertible.of_faithfullyFlat_tensorProduct (S := S)

/-- Native `IsBaseChange` interface for the invariant submodule caller. -/
theorem Invertible.of_faithfullyFlat_of_isBaseChange [FaithfullyFlat R S]
    {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Invertible S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) :
    Module.Invertible R M :=
  Invertible.of_faithfullyFlat_equiv hf.equiv
end Module
