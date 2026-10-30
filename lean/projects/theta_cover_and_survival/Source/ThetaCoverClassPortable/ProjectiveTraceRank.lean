import ThetaCoverClassPortable.ProjectiveTraceBaseChange
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.LocalProperties.Basic

namespace FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
open scoped TensorProduct
universe u v
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Constant true rank-at-stalk gives the expected identity trace over the
ORIGINAL ring, including its nilpotents. Checking only residue fields
would be insufficient; this proof uses joint injectivity of ALL actual
maximal localizations and genuine free localized modules. -/
theorem traceAlong_id_of_rankAtStalk [Module.Finite R M] [Module.Projective R M]
    (p : Frame R M) (n : ℕ) (hn : ∀q : PrimeSpectrum R,Module.rankAtStalk M q=n) :
    traceAlong p LinearMap.id=(n : R) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_localization
  intro q hq
  let S := Localization.AtPrime q
  letI := projective_tensor (R:=R) (M:=M) S
  letI : Module.Free S (S ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  have ht := traceAlong_baseChange S p (LinearMap.id : Module.End R M)
  have hr : Module.finrank S (S ⊗[R] M)=n := by
    exact (Module.rankAtStalk_eq_finrank_tensorProduct (M:=M) (⟨q,inferInstance⟩ : PrimeSpectrum R)).symm.trans (hn _)
  rw [LinearMap.baseChange_id,traceAlong_eq_free,LinearMap.trace_id,hr] at ht
  rw [map_sub,← ht,map_natCast,sub_self]

#print axioms traceAlong_id_of_rankAtStalk
end
end FourCorner.ProjectiveStabilizedDeterminant
