import ThetaCoverClassPortable.LaurentPresentationMaps
import ThetaCoverClassPortable.TwoTermFinite

noncomputable section
set_option autoImplicit false
open Polynomial
universe u
namespace FourCorner.FiniteMapCohomology
variable {R : Type u} [CommRing R]

/-- Actual Laurent-localizing finite polynomial chart modules have finite H1.
The proof constructs a standard-twist presentation and uses its PROVED finite
cohomology and the actual surjection of cokernels; it assumes no H1 finiteness. -/
theorem laurent_H1_finite (S : TwoChartCech.Sections.{u,u,u} (laurentCover R))
    [Module.Finite R[X] S.M0] [Module.Finite R[X] S.M1]
    (h0 : NegativeLocalizes S) (h1 : PositiveLocalizes S) : Module.Finite R S.H1 := by
  obtain ⟨n,a,b,⟨p⟩⟩ := exists_laurent_presentation S h0 h1
  haveI : Module.Finite R (freeTwistSections (R := R) (ι := Fin a ⊕ Fin b) (-(n:ℤ))).H1 :=
    freeTwist_finite_H1 _
  exact FourCorner.TwoTermFiniteness.finite_H1
    (freeTwistSections (R := R) (ι := Fin a ⊕ Fin b) (-(n:ℤ))).cechDiff S.cechDiff
    p.cochain0 p.cochain1 p.cochain_comm p.cochain1_surjective
end FourCorner.FiniteMapCohomology
