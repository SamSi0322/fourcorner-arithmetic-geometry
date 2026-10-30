import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Group

noncomputable section
set_option autoImplicit false
open Polynomial
namespace FourCorner.FiniteMapCohomology

variable {R A M₀ M₁ M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M₀] [Module R M₀] [Module R[X] M₀] [IsScalarTower R R[X] M₀]
  [AddCommGroup M₁] [Module R M₁] [Module R[X] M₁] [IsScalarTower R R[X] M₁]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  (t : Aˣ) (r₀ : M₀ →ₗ[R] M) (r₁ : M₁ →ₗ[R] M)
  (h₀ : ∀ (n : ℕ) (x : M₀), r₀ ((X ^ n : R[X]) • x) = (t ^ n : Aˣ) • r₀ x)
  (h₁ : ∀ (n : ℕ) (y : M₁), r₁ ((X ^ n : R[X]) • y) = ((t⁻¹) ^ n : Aˣ) • r₁ y)

/- A true Laurent-localization denominator-clearing statement on the negative
chart lifts ANY section of the positive chart to every sufficiently large
nonnegative twist. No finite cohomology or freeness is assumed. -/
include h₁ in
theorem positive_section_lifts_all_large_twists
    (hclear₁ : ∀ z : M, ∃ (k : ℕ) (y : M₁), r₁ y = ((t⁻¹) ^ k : Aˣ) • z)
    (x : M₀) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ y : M₁, r₀ x = (t ^ n : Aˣ) • r₁ y := by
  obtain ⟨k,y,hy⟩ := hclear₁ (r₀ x)
  refine ⟨k,fun n hn => ?_⟩
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨(X ^ m : R[X]) • y,?_⟩
  rw [h₁,hy]
  simp only [smul_smul]
  have hu : t ^ (k+m) * ((t⁻¹)^m * (t⁻¹)^k) = 1 := by group
  rw [hu,one_smul]

/- The symmetric actual denominator-clearing statement lifts a negative-chart
section to every sufficiently large twist on the positive chart. -/
include h₀ in
theorem negative_section_lifts_all_large_twists
    (hclear₀ : ∀ z : M, ∃ (k : ℕ) (x : M₀), r₀ x = (t ^ k : Aˣ) • z)
    (y : M₁) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ x : M₀, r₀ x = (t ^ n : Aˣ) • r₁ y := by
  obtain ⟨k,x,hx⟩ := hclear₀ (r₁ y)
  refine ⟨k,fun n hn => ?_⟩
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨(X ^ m : R[X]) • x,?_⟩
  rw [h₀,hx,smul_smul,←pow_add,Nat.add_comm m k]

/- Finitely many TRUE chart sections acquire compatible global lifts at one
common twist. With genuine polynomial generating families this is the
finite-global-generators step; it does not assume a presentation or finite H0/H1. -/
include h₀ h₁ in
theorem finite_chart_families_lift_at_common_twist
    (hclear₀ : ∀ z : M, ∃ (k : ℕ) (x : M₀), r₀ x = (t ^ k : Aˣ) • z)
    (hclear₁ : ∀ z : M, ∃ (k : ℕ) (y : M₁), r₁ y = ((t⁻¹) ^ k : Aˣ) • z)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → M₀) (b : κ → M₁) :
    ∃ n : ℕ, (∃ y : ι → M₁, ∀ i, r₀ (a i) = (t ^ n : Aˣ) • r₁ (y i)) ∧
      (∃ x : κ → M₀, ∀ j, r₀ (x j) = (t ^ n : Aˣ) • r₁ (b j)) := by
  classical
  choose N hN using fun i => positive_section_lifts_all_large_twists t r₀ r₁ h₁ hclear₁ (a i)
  choose L hL using fun j => negative_section_lifts_all_large_twists t r₀ r₁ h₀ hclear₀ (b j)
  let n := max (Finset.univ.sup N) (Finset.univ.sup L)
  have ha : ∀ i, ∃ y, r₀ (a i) = (t ^ n : Aˣ) • r₁ y := fun i =>
    hN i n ((Finset.le_sup (f := N) (Finset.mem_univ i)).trans (le_max_left _ _))
  have hb : ∀ j, ∃ x, r₀ x = (t ^ n : Aˣ) • r₁ (b j) := fun j =>
    hL j n ((Finset.le_sup (f := L) (Finset.mem_univ j)).trans (le_max_right _ _))
  choose y hy using ha
  choose x hx using hb
  exact ⟨n,⟨y,hy⟩,⟨x,hx⟩⟩


/- Genuine finite polynomial modules therefore admit a finite compatible
family whose two projections generate their actual chart modules. -/
include h₀ h₁ in
theorem finite_polynomial_generators_lift_at_common_twist
    [Module.Finite R[X] M₀] [Module.Finite R[X] M₁]
    (hclear₀ : ∀ z : M, ∃ (k : ℕ) (x : M₀), r₀ x = (t ^ k : Aˣ) • z)
    (hclear₁ : ∀ z : M, ∃ (k : ℕ) (y : M₁), r₁ y = ((t⁻¹) ^ k : Aˣ) • z) :
    ∃ (n a b : ℕ) (x : Fin a ⊕ Fin b → M₀) (y : Fin a ⊕ Fin b → M₁),
      (∀ i, r₀ (x i) = (t ^ n : Aˣ) • r₁ (y i)) ∧
      Submodule.span R[X] (Set.range x) = ⊤ ∧
      Submodule.span R[X] (Set.range y) = ⊤ := by
  classical
  obtain ⟨a,v,hv⟩ := Module.Finite.exists_fin (R := R[X]) (M := M₀)
  obtain ⟨b,w,hw⟩ := Module.Finite.exists_fin (R := R[X]) (M := M₁)
  obtain ⟨n,⟨y,hy⟩,⟨x,hx⟩⟩ := finite_chart_families_lift_at_common_twist
    t r₀ r₁ h₀ h₁ hclear₀ hclear₁ v w
  refine ⟨n,a,b,Sum.elim v x,Sum.elim y w,?_,?_,?_⟩
  · intro i
    cases i with
    | inl i => exact hy i
    | inr j => exact hx j
  · apply top_unique
    rw [←hv]
    apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    exact ⟨Sum.inl i,rfl⟩
  · apply top_unique
    rw [←hw]
    apply Submodule.span_mono
    rintro _ ⟨j,rfl⟩
    exact ⟨Sum.inr j,rfl⟩

end FourCorner.FiniteMapCohomology
