import ThetaCoverClassPortable.OrbitIdealCoaction
import ThetaCoverClassPortable.StableIdealNilpotence
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace FourCorner.FiniteRelationOrbit
open FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- All ideal conditions for rho are DERIVED for the SAME actual layer
J=I^k from its true annihilation equation, not left as extra hypotheses. -/
def lastLayerRho (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hs : letI := s.toRingHom.toAlgebra;Module.Flat A B) (k : ℕ)
    (hzero : (RingHom.ker (orbitTargetHom s t x))^(k+1)=⊥) :
    letI := orbitAlgebra s x
    ↥((RingHom.ker (orbitTargetHom s t x))^k) →ₗ[K]
      orbit s x ⊗[K] ↥((RingHom.ker (orbitTargetHom s t x))^k) :=
  orbitIdealRho s t x hgen heq hs _ (by rw [← pow_succ',hzero]) (orbit_kernel_power_stable s t x hgen heq k)

 theorem lastLayerRho_injective (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hs : letI := s.toRingHom.toAlgebra;Module.Flat A B) (k : ℕ)
    (hzero : (RingHom.ker (orbitTargetHom s t x))^(k+1)=⊥) :
    Function.Injective (lastLayerRho s t x hgen heq hs k hzero) :=
  orbitIdealRho_injective s t x hgen heq hs _ _ _

 theorem lastLayerRho_invariant_iff (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hs : letI := s.toRingHom.toAlgebra;Module.Flat A B) (k : ℕ)
    (hzero : (RingHom.ker (orbitTargetHom s t x))^(k+1)=⊥)
    (j : ↥((RingHom.ker (orbitTargetHom s t x))^k)) :
    letI := orbitAlgebra s x
    lastLayerRho s t x hgen heq hs k hzero j=(1 : orbit s x) ⊗ₜ[K] j ↔ s (j : A)=t (j : A) :=
  orbitIdealRho_invariant_iff s t x hgen heq hs _ _ _ j

end

section Field
variable {K A B : Type u} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- Original diagonal gives properness of the ACTUAL orbit ideal. -/
theorem orbit_kernel_ne_top (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T))) :
    RingHom.ker (orbitTargetHom s t x)≠⊤ := by
  intro htop
  have hmem : (1 : A)∈RingHom.ker (orbitTargetHom s t x) := by rw [htop];trivial
  have hzero : orbitTargetHom s t x 1=0 := hmem
  have h' := congrArg (orbitAugmentation s t x heq) hzero
  exact one_ne_zero (by simpa only [map_one,map_zero] using h')

/-- Any invariant of the ACTUAL positive ideal layer is zero. This proves
all containment, original-B equality, field-scalar and unit/properness
steps internally; it does NOT assume or claim rho coassociativity. -/
theorem lastLayerRho_invariant_eq_zero (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hs : letI := s.toRingHom.toAlgebra;Module.Flat A B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap K A)) (k : ℕ) (hk : 0<k)
    (hzero : (RingHom.ker (orbitTargetHom s t x))^(k+1)=⊥)
    (j : ↥((RingHom.ker (orbitTargetHom s t x))^k)) :
    letI := orbitAlgebra s x
    lastLayerRho s t x hgen heq hs k hzero j=(1 : orbit s x) ⊗ₜ[K] j → j=0 := by
  letI := orbitAlgebra s x
  intro hInv
  have hst := (lastLayerRho_invariant_iff s t x hgen heq hs k hzero j).mp hInv
  apply Subtype.ext
  change (j : A)=0
  exact FourCorner.StableIdealNilpotence.invariant_in_proper_ideal_eq_zero s t hinv _
    (orbit_kernel_ne_top s t x heq) (j : A) ((Ideal.pow_le_self (Nat.ne_of_gt hk)) j.property) hst

#print axioms lastLayerRho
#print axioms lastLayerRho_injective
#print axioms lastLayerRho_invariant_iff
#print axioms lastLayerRho_invariant_eq_zero
end Field
end FourCorner.FiniteRelationOrbit
