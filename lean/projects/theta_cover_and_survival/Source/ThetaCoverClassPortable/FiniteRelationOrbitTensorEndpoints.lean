import ThetaCoverClassPortable.FiniteRelationOrbitTensor

namespace FourCorner.FiniteRelationOrbit
open CategoryTheory FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- Exact target-coordinate formula of the ACTUAL proved orbit-pair
algebra equivalence. No coordinate identification is assumed. -/
theorem orbitTensorPair_target (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T))) (a : A) :
    letI := orbitAlgebra s x
    letI := (orbitTargetHom s t x).toAlgebra
    letI := s.toRingHom.toAlgebra
    orbitTensorPairEquiv s t x hgen heq ((1 : orbit s x) ⊗ₜ[A] t a)=
      (1 : orbit s x) ⊗ₜ[K] orbitTargetHom s t x a := by
  letI := orbitAlgebra s x
  letI := (orbitTargetHom s t x).toAlgebra
  letI := s.toRingHom.toAlgebra
  letI := RingMapTensorPushout.pointAlgebra (orbitTargetHom s t x) s.toRingHom
  letI := RingMapTensorPushout.pointAlgebra (orbitLeft s x) (orbitLeft s x)
  let e1 := RingMapTensorPushout.tensorEquiv (orbitTargetHom s t x) s.toRingHom
  let e2 := orbitPairAlgEquiv s t x hgen heq
  let e3 := RingMapTensorPushout.tensorEquiv (orbitLeft s x) (orbitLeft s x)
  have h1 : e1 ((1 : orbit s x) ⊗ₜ[A] t a)=(orbitRelationArrow s t x).hom (t a) :=
    RingMapTensorPushout.tensorEquiv_right _ _ _
  have h2 : e2 ((orbitRelationArrow s t x).hom (t a))=(orbitPairRight s x).hom (orbitTargetHom s t x a) := by
    have h := congrArg (fun f : CommRingCat.of B ⟶ orbitPair s x=>f.hom (t a)) (forward_arrow s t x heq)
    exact h.trans (RingHom.congr_fun (orbitPairArrow_target s t x heq) a)
  have h3 : e3 ((1 : orbit s x) ⊗ₜ[K] orbitTargetHom s t x a)=
      (orbitPairRight s x).hom (orbitTargetHom s t x a) :=
    RingMapTensorPushout.tensorEquiv_right _ _ _
  change e3.symm (e2 (e1 ((1 : orbit s x) ⊗ₜ[A] t a)))=_
  rw [h1,h2,← h3,AlgEquiv.symm_apply_apply]

#print axioms orbitTensorPair_target
end
end FourCorner.FiniteRelationOrbit
