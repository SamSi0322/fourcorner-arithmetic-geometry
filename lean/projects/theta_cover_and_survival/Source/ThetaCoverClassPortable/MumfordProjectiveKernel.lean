import ThetaCoverClassPortable.FibreSurjectivity
import ThetaCoverClassPortable.KernelBaseChange
import Mathlib.RingTheory.Flat.EquationalCriterion

namespace TwoChartCech.Mumford
noncomputable section
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {C0 C1 : Type v} [AddCommGroup C0] [AddCommGroup C1] [Module R C0] [Module R C1]
variable [Module.Flat R C0] [Module.Flat R C1]

/-- Exact original caller leaf, proved without a general finite free
Grothendieck/Mumford complex and without finiteness/free/projective C0/C1.
Original d-surjectivity, kernel flatness and arbitrary base-change
exactness are CONCLUSIONS derived from the true supplied hypotheses. -/
theorem projective_ker_of_fibre_surjective (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K],Function.Surjective (d.baseChange K)) :
    Module.Projective R (LinearMap.ker d) ∧
      (∀ (S : Type w) [CommRing S] [Algebra R S],Function.Bijective (TwoChartCech.kerBaseChangeHom d S)) ∧
      (∀ (K : Type u) [Field K] [Algebra R K],
        Module.finrank K (K ⊗[R] LinearMap.ker d)=Module.finrank K (LinearMap.ker (d.baseChange K))) := by
  have hd := FourCorner.MumfordKernel.surjective_of_field_fibres d hfib
  let : Module.Flat R (LinearMap.ker d) := FourCorner.MumfordKernel.flat_kernel d hd
  let : Module.FinitePresentation R (LinearMap.ker d) := Module.finitePresentation_of_finite R _
  refine ⟨Module.Flat.projective_of_finitePresentation,?_,?_⟩
  · intro S _ _
    exact FourCorner.MumfordKernel.kernel_baseChange_bijective d hd S
  · intro K _ _
    exact (LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom d K)
      (FourCorner.MumfordKernel.kernel_baseChange_bijective d hd K)).finrank_eq

#print axioms projective_ker_of_fibre_surjective
end
end TwoChartCech.Mumford

namespace TwoChartCech
noncomputable section
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {C0 C1 : Type v} [AddCommGroup C0] [AddCommGroup C1] [Module R C0] [Module R C1]
variable [Module.Flat R C0] [Module.Flat R C1]

/-- Public spelling of the native two-chart kernel bridge; the nested name above
is retained for the original geometric callers. -/
theorem Mumford_projective_ker_of_fibre_surjective (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K], Function.Surjective (d.baseChange K)) :
    Module.Projective R (LinearMap.ker d) ∧
      (∀ (A : Type w) [CommRing A] [Algebra R A],
        Function.Bijective (kerBaseChangeHom d A)) ∧
      (∀ (K : Type u) [Field K] [Algebra R K],
        Module.finrank K (K ⊗[R] LinearMap.ker d) =
          Module.finrank K (LinearMap.ker (d.baseChange K))) :=
  Mumford.projective_ker_of_fibre_surjective d hfib

#print axioms Mumford_projective_ker_of_fibre_surjective
end
end TwoChartCech
