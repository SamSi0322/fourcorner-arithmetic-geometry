import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.IsTensorProduct

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace Module.FaithfullyFlat

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- The actual invariant submodule of a descent coaction. -/
def coactionInvariants (ρ : N →ₗ[S] S ⊗[R] N) : Submodule R N :=
  LinearMap.ker (ρ.restrictScalars R - TensorProduct.mk R S N 1)

@[simp] theorem mem_coactionInvariants (ρ : N →ₗ[S] S ⊗[R] N) (n : N) :
    n ∈ coactionInvariants ρ ↔ ρ n = (1 : S) ⊗ₜ[R] n := by
  change ρ n - (1 : S) ⊗ₜ[R] n = 0 ↔ _
  exact sub_eq_zero

/-- Scalar multiplication, regarded as the tensor extension of the identity. -/
def tensorAction : S ⊗[R] N →ₗ[S] N :=
  (TensorProduct.isBaseChange R N S).lift LinearMap.id

@[simp] theorem tensorAction_tmul (s : S) (n : N) :
    tensorAction (R := R) (s ⊗ₜ n) = s • n := by
  have h := (TensorProduct.isBaseChange R N S).lift_eq (LinearMap.id : N →ₗ[R] N) n
  change tensorAction (R := R) ((1 : S) ⊗ₜ[R] n) = n at h
  rw [show s ⊗ₜ[R] n = s • ((1 : S) ⊗ₜ[R] n) by simp [smul_tmul']]
  rw [map_smul, h]

/-- Flat exactness constructs descent from a counital, coassociative coaction.
The submodule is the literal equalizer, without a pre-existing descent module. -/
theorem isBaseChange_coactionInvariants [Module.Flat R S]
    (ρ : N →ₗ[S] S ⊗[R] N)
    (hcounit : ∀ n, tensorAction (R := R) (ρ n) = n)
    (hcoassoc : ∀ n,
      (ρ.restrictScalars R).lTensor S (ρ n) =
        (TensorProduct.mk R S N 1).lTensor S (ρ n)) :
    IsBaseChange S (coactionInvariants ρ).subtype := by
  let E := coactionInvariants ρ
  let δ : N →ₗ[R] S ⊗[R] N := ρ.restrictScalars R - TensorProduct.mk R S N 1
  have hex : Function.Exact E.subtype δ := by
    rw [LinearMap.exact_iff]
    simp only [Submodule.range_subtype]
    rfl
  have htex := Module.Flat.lTensor_exact S hex
  let j := E.subtype.lTensor S
  let μ := (TensorProduct.isBaseChange R E S).lift E.subtype
  have hj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap E.subtype Subtype.val_injective
  have hρμ : ∀ x, ρ (μ x) = j x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [j, μ]
    | tmul s e =>
      have he : ρ e.val = (1 : S) ⊗ₜ[R] e.val := by
        have h := e.property
        change (ρ.restrictScalars R - TensorProduct.mk R S N 1) e.val = 0 at h
        exact sub_eq_zero.mp h
      have hμ : μ ((1 : S) ⊗ₜ[R] e) = e.val :=
        (TensorProduct.isBaseChange R E S).lift_eq E.subtype e
      rw [show s ⊗ₜ[R] e = s • ((1 : S) ⊗ₜ[R] e) by simp [smul_tmul'],
        μ.map_smul, hμ, ρ.map_smul, he]
      simp [j, smul_tmul']
    | add x y hx hy => simp [hx, hy]
  have hμinj : Function.Injective μ := by
    intro x y h
    apply hj
    rw [← hρμ, ← hρμ, h]
  have hμsurj : Function.Surjective μ := by
    intro n
    have hzero : δ.lTensor S (ρ n) = 0 := by
      simpa only [δ, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero] using hcoassoc n
    obtain ⟨x, hx⟩ := (htex (ρ n)).mp hzero
    refine ⟨x, ?_⟩
    apply_fun tensorAction (R := R) at hx
    rw [← hρμ x] at hx
    simpa only [hcounit] using hx
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective μ ⟨hμinj, hμsurj⟩)
    ((TensorProduct.isBaseChange R E S).lift_eq E.subtype)

/-- The recovered base-change equivalence intertwines the given coaction with
the canonical coaction on the descended module. -/
theorem coaction_equiv_compatible [Module.Flat R S]
    (ρ : N →ₗ[S] S ⊗[R] N)
    (hcounit : ∀ n, tensorAction (R := R) (ρ n) = n)
    (hcoassoc : ∀ n,
      (ρ.restrictScalars R).lTensor S (ρ n) =
        (TensorProduct.mk R S N 1).lTensor S (ρ n))
    (x : S ⊗[R] coactionInvariants ρ) :
    ρ ((isBaseChange_coactionInvariants ρ hcounit hcoassoc).equiv x) =
      (coactionInvariants ρ).subtype.lTensor S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s e =>
    rw [IsBaseChange.equiv_tmul, map_smul]
    change s • ρ e.val = _
    rw [(mem_coactionInvariants ρ e.val).mp e.property]
    simp [smul_tmul']
  | add x y hx hy => simp [hx, hy]

end Module.FaithfullyFlat
