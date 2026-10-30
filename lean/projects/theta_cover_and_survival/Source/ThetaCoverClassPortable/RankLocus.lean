import ThetaCoverClassPortable.FibreSurjectivityOpen
import ThetaCoverClassPortable.EulerLocalConstancy
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped TensorProduct
open Submodule
namespace FourCorner.ClosedKernelRank
open Module
universe u
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

lemma span_one_tmul (K : Type u) [Field K] [Algebra R K] :
    span K (Set.range (fun m : M => (1 : K) ⊗ₜ[R] m)) = ⊤ := by
  suffices ∀ x : K ⊗[R] M, x ∈ span K (Set.range (fun m : M => (1 : K) ⊗ₜ[R] m)) from
    le_antisymm le_top (fun x _ => this x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul a m =>
    have hm : (1 : K) ⊗ₜ[R] m ∈ span K (Set.range (fun m : M => (1 : K) ⊗ₜ[R] m)) :=
      subset_span ⟨m,rfl⟩
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using Submodule.smul_mem _ a hm

lemma exists_generators_on_fibre [Module.Finite R M]
    (K : Type u) [Field K] [Algebra R K] :
    ∃ (r : ℕ) (f : (Fin r → R) →ₗ[R] M),
      r = Module.finrank K (K ⊗[R] M) ∧ Function.Surjective (f.baseChange K) := by
  classical
  obtain ⟨ι,a,ha,hsp,hli⟩ := exists_linearIndependent' K (fun m : M => (1:K) ⊗ₜ[R] m)
  letI : Finite ι := hli.finite
  letI := Fintype.ofFinite ι
  have hs : ⊤ ≤ span K (Set.range ((fun m : M => (1:K) ⊗ₜ[R] m) ∘ a)) := by
    rw [hsp,span_one_tmul]
  let b := (Basis.mk hli hs).reindex (Fintype.equivFin ι)
  let f := Fintype.linearCombination R (a ∘ (Fintype.equivFin ι).symm)
  refine ⟨Fintype.card ι,f,(Module.finrank_eq_card_basis (Basis.mk hli hs)).symm,?_⟩
  rw [←LinearMap.range_eq_top]
  apply top_le_iff.mp
  rw [←b.span_eq]
  apply span_le.mpr
  rintro _ ⟨i,rfl⟩
  refine ⟨(1:K) ⊗ₜ[R] (Pi.single i (1:R)),?_⟩
  simp [f,LinearMap.baseChange_tmul,Fintype.linearCombination_apply_single,b]

/-- A presentation-independent generator-rank ideal. Every generator test
is a literal finite-free map into M and uses its actual cokernel. -/
def generatorRankIdeal (n : ℕ) : Ideal R :=
  ⨆ (r : ℕ) (_ : r < n) (f : (Fin r → R) →ₗ[R] M),
    Module.annihilator R (M ⧸ LinearMap.range f)

lemma rank_ge_iff_no_small_surjection [Module.Finite R M]
    (K : Type u) [Field K] [Algebra R K] (n : ℕ) :
    n ≤ Module.finrank K (K ⊗[R] M) ↔
    ∀ (r : ℕ), r < n → ∀ f : (Fin r → R) →ₗ[R] M, ¬ Function.Surjective (f.baseChange K) := by
  letI : Nontrivial R := (algebraMap R K).domain_nontrivial
  constructor
  · intro hn r hr f hf
    have hi := LinearMap.finrank_le_finrank_of_surjective hf
    have he : Module.finrank K (K ⊗[R] (Fin r → R)) = r := by
      rw [Module.finrank_baseChange,Module.finrank_pi,Fintype.card_fin]
    omega
  · intro h
    by_contra hn
    obtain ⟨r,f,hr,hf⟩ := exists_generators_on_fibre (R:=R) (M:=M) K
    exact h r (by omega) f hf

lemma fibre_rank_locus_eq [Module.Finite R M] (n : ℕ) :
    {p : PrimeSpectrum R | n ≤ Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)} =
      PrimeSpectrum.zeroLocus (generatorRankIdeal (R:=R) (M:=M) n : Set R) := by
  ext p
  simp only [Set.mem_setOf_eq]
  rw [rank_ge_iff_no_small_surjection]
  change (∀ r, r<n → ∀ f : (Fin r → R) →ₗ[R] M, ¬ Function.Surjective (f.baseChange p.asIdeal.ResidueField)) ↔
    generatorRankIdeal (R:=R) (M:=M) n ≤ p.asIdeal
  rw [generatorRankIdeal,iSup_le_iff]
  apply forall_congr'
  intro r
  rw [iSup_le_iff]
  apply forall_congr'
  intro hr
  rw [iSup_le_iff]
  apply forall_congr'
  intro f
  rw [FourCorner.FibreSurjectivity.residue_surjective_iff_not_support,not_not]
  change p ∈ Module.support R (M ⧸ LinearMap.range f) ↔ _
  rw [Module.support_eq_zeroLocus]
  rfl

theorem finite_module_isClosed_rank_ge [Module.Finite R M] (n : ℕ) :
    IsClosed {p : PrimeSpectrum R | n ≤ Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)} := by
  rw [fibre_rank_locus_eq]
  exact PrimeSpectrum.isClosed_zeroLocus _

#print axioms exists_generators_on_fibre
#print axioms finite_module_isClosed_rank_ge
end FourCorner.ClosedKernelRank
