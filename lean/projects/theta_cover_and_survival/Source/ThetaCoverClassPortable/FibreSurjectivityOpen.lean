import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

noncomputable section
open scoped TensorProduct

namespace FourCorner.FibreSurjectivity

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The actual cokernel commutes with arbitrary scalar extension. In particular,
the scalar extension need not be flat. -/
theorem cokernel_baseChange (f : M →ₗ[R] N) (S : Type*) [CommRing S] [Algebra R S] :
    Nonempty (((S ⊗[R] N) ⧸ LinearMap.range (f.baseChange S)) ≃ₗ[S]
      S ⊗[R] (N ⧸ LinearMap.range f)) := by
  let q : N →ₗ[R] N ⧸ LinearMap.range f := (LinearMap.range f).mkQ
  let qS := q.baseChange S
  have hsurj : Function.Surjective qS := q.baseChange_surjective S (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker qS = LinearMap.range (f.baseChange S) := by
    have h : LinearMap.ker (LinearMap.lTensor S q) =
        LinearMap.range (LinearMap.lTensor S f) := by
      rw [lTensor_mkQ]
      have hf : f = (LinearMap.range f).subtype ∘ₗ f.rangeRestrict := LinearMap.ext fun _ => rfl
      conv_rhs => rw [hf, LinearMap.lTensor_comp]
      rw [LinearMap.range_comp_of_range_eq_top]
      exact LinearMap.range_eq_top.mpr
        (LinearMap.lTensor_surjective S (LinearMap.surjective_rangeRestrict f))
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    have hx : qS x = LinearMap.lTensor S q x := congrFun (LinearMap.baseChange_eq_ltensor q) x
    rw [hx, ← LinearMap.mem_ker, h, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, congrFun (LinearMap.baseChange_eq_ltensor f) y⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor f) y).symm⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (qS.quotKerEquivOfSurjective hsurj)⟩

theorem surjective_baseChange_iff (f : M →ₗ[R] N) (S : Type*) [CommRing S] [Algebra R S] :
    Function.Surjective (f.baseChange S) ↔ Subsingleton (S ⊗[R] (N ⧸ LinearMap.range f)) := by
  obtain ⟨e⟩ := cokernel_baseChange f S
  rw [← e.toEquiv.subsingleton_congr, Submodule.Quotient.subsingleton_iff,
    LinearMap.range_eq_top]

/-- Only the cokernel is finite: neither term of the map is required finite,
flat, or projective, and the base ring need not be Noetherian. -/
theorem residue_surjective_iff_not_support (f : M →ₗ[R] N)
    [Module.Finite R (N ⧸ LinearMap.range f)] (p : PrimeSpectrum R) :
    Function.Surjective (f.baseChange p.asIdeal.ResidueField) ↔
      p ∉ Module.support R (N ⧸ LinearMap.range f) := by
  rw [surjective_baseChange_iff,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    not_nontrivial_iff_subsingleton]

end FourCorner.FibreSurjectivity

/-- The genuine residue-field surjectivity locus is open when its cokernel
is finite. This includes nonflat residue extensions and the empty spectrum. -/
theorem LinearMap.isOpen_setOf_surjective_baseChange_residueField
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    [Module.Finite R (N ⧸ LinearMap.range f)] :
    IsOpen {p : PrimeSpectrum R | Function.Surjective (f.baseChange p.asIdeal.ResidueField)} := by
  have heq : {p : PrimeSpectrum R | Function.Surjective (f.baseChange p.asIdeal.ResidueField)} =
      (Module.support R (N ⧸ LinearMap.range f))ᶜ := by
    ext p
    exact FourCorner.FibreSurjectivity.residue_surjective_iff_not_support f p
  rw [heq, Module.support_eq_zeroLocus]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
