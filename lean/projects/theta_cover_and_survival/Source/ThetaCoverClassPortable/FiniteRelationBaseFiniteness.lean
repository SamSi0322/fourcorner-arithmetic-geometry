import ThetaCoverClassPortable.FiniteRelationIntegrality
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

namespace FourCorner.FiniteRelationQuotient
noncomputable section
universe u
variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra C A]

/-- An actual common base map factors through the exact invariant ring.
The map is constructed, not added as a tower/quotient hypothesis. -/
def invariantBaseMap (s t : A →+* B)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap R A)=t.comp (algebraMap R A)) : R →+* C :=
  (invariantRingEquiv s t hinj hinv).symm.toRingHom.comp
    ((algebraMap R A).codRestrict (s.eqLocus t) (fun r=>RingHom.congr_fun hbase r))

abbrev invariantBaseAlgebra (s t : A →+* B)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap R A)=t.comp (algebraMap R A)) : Algebra R C :=
  (invariantBaseMap s t hinj hinv hbase).toAlgebra

 theorem invariantBaseMap_comp (s t : A →+* B)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap R A)=t.comp (algebraMap R A)) (r : R) :
    algebraMap C A (invariantBaseMap s t hinj hinv hbase r)=algebraMap R A r := by
  have h := congrArg Subtype.val ((invariantRingEquiv s t hinj hinv).apply_symm_apply
    (⟨algebraMap R A r,RingHom.congr_fun hbase r⟩ : s.eqLocus t))
  exact h

 theorem invariantBaseTower (s t : A →+* B)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap R A)=t.comp (algebraMap R A)) :
    letI := invariantBaseAlgebra s t hinj hinv hbase
    IsScalarTower R C A := by
  letI := invariantBaseAlgebra s t hinj hinv hbase
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (invariantBaseMap_comp s t hinj hinv hbase r).symm

/-- Genuine usable finite-type specialization: A is finite over its exact
invariants, when the common base makes A finite type. No noetherian,
field, freeness, quotient effectiveness, or C-flatness input is assumed. -/
theorem finite_of_common_finiteType_base (s t : A →+* B)
    (hfinite : letI := s.toAlgebra; Module.Finite A B)
    (hprojective : letI := s.toAlgebra; Module.Projective A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap R A)=t.comp (algebraMap R A))
    [Algebra.FiniteType R A] : Module.Finite C A := by
  letI := invariantBaseAlgebra s t hinj hinv hbase
  letI := invariantBaseTower s t hinj hinv hbase
  letI : Algebra.FiniteType C A := Algebra.FiniteType.of_restrictScalars_finiteType R C A
  letI : Algebra.IsIntegral C A := ⟨integral_of_finiteProjective_relation s t hfinite hprojective hgen heq hinj hinv⟩
  exact Algebra.IsIntegral.finite

#print axioms invariantBaseMap_comp
#print axioms invariantBaseTower
#print axioms finite_of_common_finiteType_base
end
end FourCorner.FiniteRelationQuotient
