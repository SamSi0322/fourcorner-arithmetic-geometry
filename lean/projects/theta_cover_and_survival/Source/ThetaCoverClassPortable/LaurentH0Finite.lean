import ThetaCoverClassPortable.LaurentKernelLocalizations
import ThetaCoverClassPortable.LaurentH1Finite

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
universe u
namespace FourCorner.FiniteMapCohomology
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Actual finite polynomial chart modules with Laurent-localizing
restrictions have finite H0. The constructed standard-twist presentation
has an actual kernel, whose polynomial finiteness follows from Noetherianity.
Native exactness of localization gives a second standard-twist presentation
of that kernel; its H1 is finite by the proved cokernel surjection. The
actual two-term connecting map and its proved exactness finish H0. -/
theorem laurent_H0_finite (S : TwoChartCech.Sections.{u,u,u} (laurentCover R))
    [Module.Finite R[X] S.M0] [Module.Finite R[X] S.M1]
    (h0 : NegativeLocalizes S) (h1 : PositiveLocalizes S) : Module.Finite R S.H0 := by
  obtain ⟨n,a,b,⟨p⟩⟩ := exists_laurent_presentation S h0 h1
  haveI := p.kernel_finite_negative
  haveI := p.kernel_finite_positive
  haveI : Module.Finite R p.kernelSections.H1 := laurent_H1_finite p.kernelSections
    (p.kernel_negative_localizes h0) (p.kernel_positive_localizes h1)
  haveI : Module.Finite R (freeTwistSections (R := R) (ι := Fin a ⊕ Fin b) (-(n:ℤ))).H0 :=
    freeTwist_finite_H0 _
  exact FourCorner.TwoTermFiniteness.finite_H0 p.kernelSections.cechDiff
    (freeTwistSections (R := R) (ι := Fin a ⊕ Fin b) (-(n:ℤ))).cechDiff S.cechDiff
    p.kernelInclusion0 p.kernelInclusion1 p.cochain0 p.cochain1
    p.kernelInclusion1_injective p.cochain0_surjective p.kernel_exact0 p.kernel_exact1
    p.kernel_cochain_comm p.cochain_comm
end FourCorner.FiniteMapCohomology
