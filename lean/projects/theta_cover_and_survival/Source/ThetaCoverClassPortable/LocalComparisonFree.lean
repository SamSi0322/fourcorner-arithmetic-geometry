import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped TensorProduct
namespace FourCorner.QuotientLocalFree
universe u
variable {C A B : Type u} [CommRing C] [CommRing A] [CommRing B]
  [Algebra C A] [Algebra A B]

/-- Genuine local closure of the quotient-algebra leaf. The base C is NOT assumed flat
in A. Actual fibre basis lifting, projectivity/rank over A and coefficient injectivity
construct a real C-basis and prove bijectivity of the given actual comparison. -/
theorem local_free_and_comparison_bijective [IsLocalRing C] [Module.Finite C A]
    [Module.Finite A B] [Module.Projective A B]
    (hinj : Function.Injective (algebraMap C A)) (n : ℕ)
    (hrank : ∀ p : PrimeSpectrum A, Module.rankAtStalk (R := A) B p = n)
    (Can : A ⊗[C] A →ₐ[A] B) (hCan : Function.Surjective Can)
    (hdim : Module.finrank (IsLocalRing.ResidueField C)
      (IsLocalRing.ResidueField C ⊗[C] A) = n) :
    ∃ b : Module.Basis (Fin n) C A, Function.Bijective Can := by
  classical
  haveI : Nontrivial A := hinj.nontrivial
  let k := IsLocalRing.ResidueField C
  let b := Module.finBasisOfFinrankEq k (k ⊗[C] A) hdim
  have hmk : Function.Surjective (TensorProduct.mk C k A 1) :=
    TensorProduct.mk_surjective C A k IsLocalRing.residue_surjective
  choose v hv using fun i : Fin n => hmk (b i)
  have hspan : Submodule.span C (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv
  let P := Fin n →₀ C
  let f : P →ₗ[C] A := Finsupp.linearCombination C v
  have hfs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    exact (Finsupp.range_linearCombination C).trans hspan
  have hts : Function.Surjective (f.baseChange A) := f.lTensor_surjective A hfs
  let g : A ⊗[C] P →ₗ[A] B := Can.toLinearMap.comp (f.baseChange A)
  have hgs : Function.Surjective g := hCan.comp hts
  haveI : Module.Flat A B := inferInstance
  have hrankP : Module.rankAtStalk (R := A) (A ⊗[C] P) = n := by
    rw [Module.rankAtStalk_eq_finrank_of_free]
    simp [P]
  have hgb : Function.Bijective g :=
    Module.bijective_of_surjective_of_rankAtStalk_eq hgs (fun p _ => by
      exact (congrFun hrankP ⟨p, inferInstance⟩).trans (hrank ⟨p, inferInstance⟩).symm)
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have ht : (1 : A) ⊗ₜ[C] z = (0 : A ⊗[C] P) := by
      apply hgb.1
      simp only [g, LinearMap.comp_apply, LinearMap.baseChange_tmul, hz,
        TensorProduct.tmul_zero, map_zero]
    ext i
    apply hinj
    let ev : P →ₗ[C] C := Finsupp.lapply i
    have hc := congrArg (fun w : A ⊗[C] P =>
      TensorProduct.rid C A ((ev.baseChange A) w)) ht
    have hc' : algebraMap C A (ev z) = 0 := by
      simpa only [LinearMap.baseChange_tmul, TensorProduct.rid_tmul, Algebra.smul_def,
        mul_one, map_zero] using hc
    change algebraMap C A (z i) = 0 at hc'
    simpa using hc'
  have hci : Function.Injective Can := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := hts x
    obtain ⟨y', rfl⟩ := hts y
    exact congrArg (f.baseChange A) (hgb.1 hxy)
  exact ⟨Module.Basis.ofRepr (LinearEquiv.ofBijective f ⟨hfi, hfs⟩).symm, hci, hCan⟩
end FourCorner.QuotientLocalFree
