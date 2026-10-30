import ThetaCoverClassPortable.FiniteRelationComparison

namespace FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]

/-- Actual source tower, with both original scalar maps retained. -/
def sourceScalarTower (s : A →+* B) :
    letI := s.toAlgebra
    letI := relationAlgebra (C:=C) s
    IsScalarTower C A B := by
  letI := s.toAlgebra
  letI := relationAlgebra (C:=C) s
  exact IsScalarTower.of_algebraMap_eq (fun _=>rfl)

/-- Upgrade of the SAME canonical tensor comparison to an actual
A-algebra map for the FIRST tensor/source action. The second A leg is
still the original t, never a default same-Type A-action. -/
def canonicalAComparison (s t : A →+* B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A)) :
    letI := s.toAlgebra
    letI := relationAlgebra (C:=C) s
    A ⊗[C] A →ₐ[A] B := by
  letI := s.toAlgebra
  letI := relationAlgebra (C:=C) s
  exact { (canonicalComparison s t hinv).toRingHom with commutes':=fun a=>comparison_left s t hinv a }

 theorem canonicalAComparison_tmul (s t : A →+* B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A)) (a b : A) :
    canonicalAComparison s t hinv (a ⊗ₜ[C] b)=s a*t b := by
  letI := s.toAlgebra
  letI := relationAlgebra (C:=C) s
  change canonicalComparison s t hinv (a ⊗ₜ[C] b)=_
  rw [canonicalComparison,Algebra.TensorProduct.lift_tmul]
  rfl

 theorem canonicalAComparison_surjective (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A)) :
    Function.Surjective (canonicalAComparison s t hinv) := canonicalComparison_surjective s t hgen hinv

 theorem canonicalAComparison_right (s t : A →+* B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A)) (a : A) :
    canonicalAComparison s t hinv ((1 : A) ⊗ₜ[C] a)=t a := comparison_right s t hinv a

#print axioms sourceScalarTower
#print axioms canonicalAComparison
#print axioms canonicalAComparison_tmul
#print axioms canonicalAComparison_surjective
end
end FourCorner.FiniteRelationQuotient
