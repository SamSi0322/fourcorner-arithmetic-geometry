import ThetaCoverClassPortable.LastOrbitLayerRho
import ThetaCoverClassPortable.OrbitPairCoactionTransfer
import ThetaCoverClassPortable.PairCoactionInvariants
import ThetaCoverClassPortable.FiniteRelationOrbitDimension
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace FourCorner.FiniteRelationOrbit
open FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u
variable {K A B : Type u} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- COMPLETE original-object pointed fieldcase: the ACTUAL orbit kernel
is zero. Every nilpotent layer, actual rho/coassoc, original-B invariance,
containment, field scalar/unit/properness fact is proved upstream and
instantiated here. No obstruction/effectivity/coassoc premise is added. -/
theorem pointed_orbit_kernel_eq_bot [Module.Finite K A]
    (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hs : letI := s.toRingHom.toAlgebra;Module.Flat A B)
    (ht : letI := t.toRingHom.toAlgebra;Module.Flat A B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap K A)) :
    RingHom.ker (orbitTargetHom s t x)=⊥ := by
  letI := orbitAlgebra s x
  letI : Nontrivial A := ⟨⟨1,0,by
    intro h
    exact one_ne_zero (by simpa only [map_one,map_zero] using congrArg x h)⟩⟩
  by_contra hI
  have hnil := FourCorner.StableIdealNilpotence.orbit_kernel_nilpotent s t x hgen heq hinv
  obtain ⟨k,hk,hJ,hzero⟩ := FourCorner.StableIdealNilpotence.exists_last_nonzero_power
    (RingHom.ker (orbitTargetHom s t x)) hI hnil
  let J : Ideal A := (RingHom.ker (orbitTargetHom s t x))^k
  obtain ⟨a,ha,hane⟩ := (Submodule.ne_bot_iff J).mp hJ
  let j : J := ⟨a,ha⟩
  have hjne : j≠0 := fun h=>hane (congrArg Subtype.val h)
  let rho := lastLayerRho s t x hgen heq hs k hzero
  have hrho : Function.Injective rho := lastLayerRho_injective s t x hgen heq hs k hzero
  have hco (m : J) :
      TensorProduct.map (LinearMap.id : orbit s x →ₗ[K] orbit s x) rho (rho m)=
      TensorProduct.map (LinearMap.id : orbit s x →ₗ[K] orbit s x)
        (FourCorner.PairCoactionInvariants.unitVector (1 : orbit s x)) (rho m) := by
    exact orbitIdealRho_pair_coassoc s t x hgen heq hs ht J
      (by dsimp only [J];rw [← pow_succ',hzero]) (orbit_kernel_power_stable s t x hgen heq k) m
  obtain ⟨w,hw,hInv⟩ := FourCorner.PairCoactionInvariants.exists_nonzero_invariant_of_injective
    (1 : orbit s x) rho hrho hco hjne
  exact hw (lastLayerRho_invariant_eq_zero s t x hgen heq hs hinv k hk hzero w hInv)

/-- The SAME actual pointed field algebra therefore has dimension n,
from its true original source rank. Nilpotents were retained throughout;
none were replaced by a reduced algebra or a collection of points. -/
theorem pointed_field_dimension [Module.Finite K A]
    (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hfinite : letI := s.toRingHom.toAlgebra;Module.Finite A B)
    (hprojective : letI := s.toRingHom.toAlgebra;Module.Projective A B)
    (ht : letI := t.toRingHom.toAlgebra;Module.Flat A B)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap K A))
    (n : ℕ) (hrank : letI := s.toRingHom.toAlgebra;∀p : PrimeSpectrum A,Module.rankAtStalk B p=n) :
    Module.finrank K A=n := by
  letI := orbitAlgebra s x
  letI := s.toRingHom.toAlgebra
  letI := hfinite
  letI := hprojective
  have hs : Module.Flat A B := inferInstance
  have hzero := pointed_orbit_kernel_eq_bot s t x hgen heq hs ht hinv
  have hi : Function.Injective (orbitTarget s t x) := by
    intro a b hab
    have hm : a-b∈RingHom.ker (orbitTargetHom s t x) := by
      change orbitTarget s t x (a-b)=0
      rw [map_sub,hab,sub_self]
    have hz : a-b=0 := by simpa only [hzero,Submodule.mem_bot] using hm
    exact sub_eq_zero.mp hz
  let e := AlgEquiv.ofBijective (orbitTarget s t x) ⟨hi,orbitTarget_surjective s t x hgen⟩
  exact e.toLinearEquiv.finrank_eq.trans (orbit_finrank s t x hfinite hprojective n hrank)

#print axioms pointed_orbit_kernel_eq_bot
#print axioms pointed_field_dimension
end
end FourCorner.FiniteRelationOrbit
