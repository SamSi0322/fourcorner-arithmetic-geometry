import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.RingTheory.Flat.Basic

noncomputable section
set_option autoImplicit false
universe u v
namespace FourCorner.ActualPicardProperties

/-- Every module over the actual finite reduced rational base is flat.
This includes the zero algebra. -/
theorem finite_reduced_QQ_module_flat
    (A : Type u) [CommRing A] [Algebra ℚ A] [Module.Finite ℚ A] [IsReduced A]
    (M : Type v) [AddCommGroup M] [Module A M] : Module.Flat A M := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℚ A
  haveI : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_of_isReduced A
  haveI : Module.Projective A M := Module.projective_of_isSemisimpleRing A M
  infer_instance

/-- The same actual base has finitely many scheme points. -/
theorem finite_reduced_QQ_primeSpectrum_finite
    (A : Type u) [CommRing A] [Algebra ℚ A] [Module.Finite ℚ A] [IsReduced A] :
    Finite (PrimeSpectrum A) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℚ A
  infer_instance

#print axioms finite_reduced_QQ_module_flat
end FourCorner.ActualPicardProperties
