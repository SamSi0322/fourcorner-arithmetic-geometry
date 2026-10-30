import ThetaCoverClassPortable.CoactionEqualizer
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
set_option autoImplicit false
open TensorProduct
universe u
namespace FourCorner.FlatAlgebraEqualizer
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

/-- The literal algebra equalizer of a genuine counital coaction. -/
def invariants (ρ : A →ₐ[S] S ⊗[R] A) : Subalgebra R A :=
  AlgHom.equalizer (ρ.restrictScalars R)
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)

@[simp] theorem mem_invariants (ρ : A →ₐ[S] S ⊗[R] A) (a : A) :
    a ∈ invariants ρ ↔ ρ a = (1:S) ⊗ₜ[R] a := by
  rfl

/-- The actual scalar-extension ring map, on pure tensors s tensor a ↦ s*a. -/
def canonical (ρ : A →ₐ[S] S ⊗[R] A) : S ⊗[R] invariants ρ →ₐ[S] A :=
  { (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S A)
      (invariants ρ).val (fun _ _=>Commute.all _ _)).toRingHom with
    commutes' := by
      intro s
      change (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S A)
        (invariants ρ).val (fun _ _=>Commute.all _ _)) (s ⊗ₜ[R] 1)=algebraMap S A s
      rw [Algebra.TensorProduct.lift_tmul]
      change algebraMap S A s * 1=algebraMap S A s
      exact mul_one _ }

@[simp] theorem canonical_tmul (ρ : A →ₐ[S] S ⊗[R] A) (s:S) (a:invariants ρ) :
    canonical ρ (s ⊗ₜ[R] a)=s • (a:A) := by
  change algebraMap S A s * (a:A)=_
  exact (Algebra.smul_def s (a:A)).symm

/-- Flat module descent proves bijectivity of this REAL ring map. No
pre-existing descended module, algebra, or quotient is supplied. -/
theorem canonical_bijective [Module.Flat R S] (ρ : A →ₐ[S] S ⊗[R] A)
    (hc : ∀ a, Module.FaithfullyFlat.tensorAction (R:=R) (ρ a)=a)
    (ha : ∀ a, (ρ.toLinearMap.restrictScalars R).lTensor S (ρ a)=
      (TensorProduct.mk R S A 1).lTensor S (ρ a)) :
    Function.Bijective (canonical ρ) := by
  have hE : (invariants ρ).toSubmodule = Module.FaithfullyFlat.coactionInvariants ρ.toLinearMap := by
    ext a
    exact (mem_invariants ρ a).trans (Module.FaithfullyFlat.mem_coactionInvariants ρ.toLinearMap a).symm
  have hb : IsBaseChange S (invariants ρ).toSubmodule.subtype := by
    rw [hE]
    exact Module.FaithfullyFlat.isBaseChange_coactionInvariants ρ.toLinearMap hc ha
  have he : (canonical ρ : S ⊗[R] invariants ρ → A)=hb.equiv := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add,map_add,hx,hy]
    | tmul s a =>
      rw [canonical_tmul]
      erw [IsBaseChange.equiv_tmul]
      rfl
  rw [he]
  exact hb.equiv.bijective

/-- The actual affine descended algebra and its canonical base-change isomorphism. -/
def equivalence [Module.Flat R S] (ρ : A →ₐ[S] S ⊗[R] A)
    (hc : ∀ a, Module.FaithfullyFlat.tensorAction (R:=R) (ρ a)=a)
    (ha : ∀ a, (ρ.toLinearMap.restrictScalars R).lTensor S (ρ a)=
      (TensorProduct.mk R S A 1).lTensor S (ρ a)) :
    S ⊗[R] invariants ρ ≃ₐ[S] A :=
  AlgEquiv.ofBijective (canonical ρ) (canonical_bijective ρ hc ha)
end FourCorner.FlatAlgebraEqualizer
