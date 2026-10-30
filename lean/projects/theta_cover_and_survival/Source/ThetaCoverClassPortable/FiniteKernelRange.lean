import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Finsupp

set_option autoImplicit false
namespace FourCorner.FiniteMapCohomology
variable {R A B C : Type*} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- A finite image bound on the actual kernel and a finite target imply
finiteness of the middle module over a Noetherian base. -/
theorem finite_of_ker_le_range (f : B →ₗ[R] C) (g : A →ₗ[R] B)
    [Module.Finite R A] [Module.Finite R C]
    (h : LinearMap.ker f ≤ LinearMap.range g) : Module.Finite R B := by
  letI : Module.Finite R (LinearMap.range g) := Module.Finite.range g
  letI : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  letI : Module.Finite R (B ⧸ LinearMap.ker f) :=
    Module.Finite.equiv (LinearMap.quotKerEquivRange f).symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)

end FourCorner.FiniteMapCohomology
