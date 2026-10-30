import ThetaCoverClassPortable.GaloisTensorInvariant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.Topology.Algebra.MulAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct Pointwise
namespace FourCorner.ThetaLocalSurvival.ComponentDescent

abbrev Omega := AlgebraicClosure ℚ
abbrev GaloisGroup := Omega ≃ₐ[ℚ] Omega
local instance : IsGalois ℚ Omega := ⟨⟩
local instance : TopologicalSpace Omega := ⊥
local instance : DiscreteTopology Omega := ⟨rfl⟩
local instance : ContinuousSMul GaloisGroup Omega :=
  continuousSMul_iff_stabilizer_isOpen.mpr (fun x => stabilizer_isOpen_of_isIntegral x)

variable (A : Type) [CommRing A] [Algebra ℚ A]
attribute [local instance high] Algebra.TensorProduct.rightAlgebra

instance tensor_scalar_comm : SMulCommClass GaloisGroup A (tensorRing Omega A) := by
  constructor
  intro σ a x
  simp only [Algebra.smul_def,tensor_smul]
  rw [map_mul]
  have h : tensorAut Omega A σ (algebraMap A (tensorRing Omega A) a)=
      algebraMap A (tensorRing Omega A) a := by
    change tensorAut Omega A σ (1 ⊗ₜ[ℚ] a)=1 ⊗ₜ[ℚ] a
    rw [tensorAut_tmul,map_one]
  rw [h]

instance tensor_invariant : Algebra.IsInvariant A (tensorRing Omega A) GaloisGroup := by
  constructor
  intro x hx
  obtain ⟨a,ha⟩ := tensor_fixed_descends (L:=Omega) (A:=A) x hx
  exact ⟨a,ha⟩

local instance : TopologicalSpace (tensorRing Omega A) := ⊥
local instance : DiscreteTopology (tensorRing Omega A) := ⟨rfl⟩
local instance : ContinuousSMul GaloisGroup (tensorRing Omega A) := by
  constructor
  rw [continuous_prod_of_discrete_right]
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simpa only [smul_zero] using (continuous_const : Continuous (fun _ : GaloisGroup => (0:tensorRing Omega A)))
  | tmul l a =>
    have hfield : Continuous (fun σ : GaloisGroup => σ l) := continuous_id.smul continuous_const
    have hmap : Continuous (fun y : Omega => y ⊗ₜ[ℚ] a) := continuous_of_discreteTopology
    change Continuous (fun σ : GaloisGroup => σ l ⊗ₜ[ℚ] a)
    exact hmap.comp hfield
  | add x y hx hy =>
    simp only [smul_add]
    exact hx.add hy

/-- Actual profinite Galois transitivity on affine scalar-extension
prime fibres, with invariance and continuity PROVED from coordinate
coefficients rather than supplied as descent flags. -/
theorem tensor_prime_fibre_transitive (P Q : Ideal (tensorRing Omega A)) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under A=Q.under A) : ∃σ : GaloisGroup,Q=σ • P :=
  Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A:=A) (G:=GaloisGroup) P Q hPQ

end FourCorner.ThetaLocalSurvival.ComponentDescent
