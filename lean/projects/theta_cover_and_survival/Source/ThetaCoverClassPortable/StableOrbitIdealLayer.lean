import ThetaCoverClassPortable.ModuleSurjectiveScalars
import ThetaCoverClassPortable.StableIdealTransport

namespace FourCorner.FiniteRelationOrbit
open FourCorner.FiniteRelationQuotient
noncomputable section
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

 theorem orbit_kernel_power_stable (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T))) (k : ℕ) :
    Ideal.map s.toRingHom ((RingHom.ker (orbitTargetHom s t x))^k)=
      Ideal.map t.toRingHom ((RingHom.ker (orbitTargetHom s t x))^k) := by
  rw [Ideal.map_pow,Ideal.map_pow,orbit_kernel_stable s t x hgen heq]

/-- The actual ideal J=I^k is made a module over the ACTUAL orbit D by
the true equation I^(k+1)=0. No annihilation/module structure is assumed
independently of that original ideal equation. -/
def orbitLayerModule (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤) (k : ℕ)
    (hzero : (RingHom.ker (orbitTargetHom s t x))^(k+1)=⊥) :
    Module (orbit s x) ↥((RingHom.ker (orbitTargetHom s t x))^k) := by
  apply FourCorner.ModuleSurjectiveScalars.idealLayerModule (orbitTargetHom s t x)
    (orbitTarget_surjective s t x hgen) ((RingHom.ker (orbitTargetHom s t x))^k)
  rw [← pow_succ',hzero]

/-- Source/target transport of this SAME actual ideal layer, retaining the
two actual A-module structures on B. -/
def orbitLayerTransport (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hs : letI := s.toRingHom.toAlgebra;Module.Flat A B)
    (ht : letI := t.toRingHom.toAlgebra;Module.Flat A B) (k : ℕ) :
    FourCorner.StableIdealTransport.tensorAlong s.toRingHom ((RingHom.ker (orbitTargetHom s t x))^k) ≃ₗ[B]
      FourCorner.StableIdealTransport.tensorAlong t.toRingHom ((RingHom.ker (orbitTargetHom s t x))^k) :=
  FourCorner.StableIdealTransport.transport s.toRingHom t.toRingHom hs ht _ (orbit_kernel_power_stable s t x hgen heq k)

#print axioms orbit_kernel_power_stable
#print axioms orbitLayerModule
#print axioms orbitLayerTransport
end
end FourCorner.FiniteRelationOrbit
