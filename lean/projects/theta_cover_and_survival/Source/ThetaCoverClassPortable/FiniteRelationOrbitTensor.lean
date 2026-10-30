import ThetaCoverClassPortable.FiniteRelationOrbitPair

namespace FourCorner.FiniteRelationOrbit
open CategoryTheory FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- The actual native orbit-pair isomorphism is OVER the first D factor,
so it really acts on the original pulled-back ideal modules. -/
def orbitPairAlgEquiv (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T))) :
    letI := RingMapTensorPushout.pointAlgebra (orbitTargetHom s t x) s.toRingHom
    letI := RingMapTensorPushout.pointAlgebra (orbitLeft s x) (orbitLeft s x)
    orbitRelation s t x ≃ₐ[orbit s x] orbitPair s x := by
  letI := RingMapTensorPushout.pointAlgebra (orbitTargetHom s t x) s.toRingHom
  letI := RingMapTensorPushout.pointAlgebra (orbitLeft s x) (orbitLeft s x)
  apply AlgEquiv.ofRingEquiv (f:=(orbitPairIso s t x hgen heq).commRingCatIsoToRingEquiv)
  intro d
  exact congrArg (fun f : orbit s x ⟶ orbitPair s x=>f.hom d) (forward_left s t x heq)

/-- GENUINE original-source algebra identification D tensor_A B ≃
D tensor_K D, with all nilpotents and the true first D scalar structure. -/
def orbitTensorPairEquiv (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T))) :
    letI := orbitAlgebra s x
    letI := (orbitTargetHom s t x).toAlgebra
    letI := s.toRingHom.toAlgebra
    orbit s x ⊗[A] B ≃ₐ[orbit s x] orbit s x ⊗[K] orbit s x := by
  letI := orbitAlgebra s x
  letI := (orbitTargetHom s t x).toAlgebra
  letI := s.toRingHom.toAlgebra
  letI := RingMapTensorPushout.pointAlgebra (orbitTargetHom s t x) s.toRingHom
  letI := RingMapTensorPushout.pointAlgebra (orbitLeft s x) (orbitLeft s x)
  exact ((RingMapTensorPushout.tensorEquiv (orbitTargetHom s t x) s.toRingHom).trans
    (orbitPairAlgEquiv s t x hgen heq)).trans
      (RingMapTensorPushout.tensorEquiv (orbitLeft s x) (orbitLeft s x)).symm

#print axioms orbitPairAlgEquiv
#print axioms orbitTensorPairEquiv
end
end FourCorner.FiniteRelationOrbit
