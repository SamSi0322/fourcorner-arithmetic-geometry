import Mathlib.RingTheory.Ideal.GoingUp

namespace FourCorner.IntegralEvaluationInjection
variable {R A L : Type*} [CommRing R] [Nontrivial R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.IsIntegral R A] [CommRing L]

/-- An integral DOMAIN's ring map is injective as soon as its restriction
to the coefficient domain is injective. Used for genuine fraction-field lifts. -/
theorem injective_of_base (f : A →+* L)
    (hf : Function.Injective (f.comp (algebraMap R A))) : Function.Injective f := by
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply Ideal.eq_bot_of_comap_eq_bot (R := R)
  change RingHom.ker (f.comp (algebraMap R A)) = ⊥
  exact (RingHom.injective_iff_ker_eq_bot _).mp hf

end FourCorner.IntegralEvaluationInjection
#print axioms FourCorner.IntegralEvaluationInjection.injective_of_base
