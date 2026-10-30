import ThetaDGeometricModel
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

namespace FourCorner.ThetaGenericRankFraction
noncomputable section
open scoped nonZeroDivisors
variable (R : Type*) [CommRing R] [IsDomain R]

def genericPrime : PrimeSpectrum R := ⟨⊥,Ideal.bot_prime⟩

theorem rankAtGeneric_eq_finrank (M : Type*) [AddCommGroup M] [Module R M] :
    Module.rankAtStalk (R:=R) M (genericPrime R)=Module.finrank R M := by
  let p := genericPrime R
  have hM : p.asIdeal.primeCompl ≤ R⁰ := by
    intro r hr
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    simpa [p,genericPrime] using hr
  change Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)=_
  trans Module.finrank R (LocalizedModule p.asIdeal.primeCompl M)
  · exact IsLocalization.finrank_eq _ _ hM
  · exact IsLocalizedModule.finrank_eq p.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ M) hM

variable (F S E : Type*) [Field F] [CommRing S] [IsDomain S] [Field E]
  [Algebra R S] [Algebra R F] [Algebra S E] [Algebra R E] [Algebra F E]
  [IsScalarTower R F E] [IsScalarTower R S E] [IsFractionRing R F] [IsFractionRing S E]

/-- Exact field degree of the actual fraction fields equals the actual
module rank of the affine ring map at its native generic prime. -/
theorem field_finrank_eq_generic_rank :
    Module.finrank F E=Module.rankAtStalk (R:=R) S (genericPrime R) := by
  rw [rankAtGeneric_eq_finrank]
  exact IsFractionRing.finrank_eq R F S E

#print axioms rankAtGeneric_eq_finrank
#print axioms field_finrank_eq_generic_rank
end
end FourCorner.ThetaGenericRankFraction
