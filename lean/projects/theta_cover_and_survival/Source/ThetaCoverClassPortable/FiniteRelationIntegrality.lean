import ThetaCoverClassPortable.FiniteRelationInvariantCharpoly
import ThetaCoverClassPortable.FiniteRelationComparison
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

namespace FourCorner.FiniteRelationQuotient
open Polynomial FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]

/-- Every element of the ACTUAL source A is integral over the EXACT
invariant ring C. The only finite-projective input is B as the source
A-module, retained with its original algebra structure. -/
theorem integral_of_finiteProjective_relation (s t : A →+* B)
    (hfinite : letI := s.toAlgebra; Module.Finite A B)
    (hprojective : letI := s.toAlgebra; Module.Projective A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A)) (a : A) : IsIntegral C a := by
  letI := s.toAlgebra
  letI := hfinite
  letI := hprojective
  let p := ofFiniteProjective A B
  let P := relationPolynomial s t p a
  have hcoeff : ∀n : ℕ,P.coeff n∈Set.range (algebraMap C A) := by
    intro n
    apply (hinv _).mp
    have h := congrArg (fun Q : B[X]=>Q.coeff n) (relationPolynomial_invariant s t hgen heq p a)
    simpa only [P,coeff_map] using h
  obtain ⟨Q,hQ⟩ := (mem_lifts P).mp ((lifts_iff_coeff_lifts P).mpr hcoeff)
  refine ⟨Q,monic_of_injective hinj (hQ.symm ▸ relationPolynomial_monic s t p a),?_⟩
  rw [eval₂_eq_eval_map,hQ]
  exact relationPolynomial_eval_self s t heq p a

#print axioms integral_of_finiteProjective_relation
end
end FourCorner.FiniteRelationQuotient
