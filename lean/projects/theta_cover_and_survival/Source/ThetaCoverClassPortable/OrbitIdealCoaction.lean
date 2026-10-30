import ThetaCoverClassPortable.IdealPairCoordinates
import ThetaCoverClassPortable.IdealLayerScalarTowers
import ThetaCoverClassPortable.FiniteRelationOrbitTensorEndpoints

namespace FourCorner.FiniteRelationOrbit
open FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- K-linear coordinates on the SAME actual ideal J·B⊂B. Every scalar
action and the pair algebra identification is actually constructed. -/
def orbitIdealCoordinates (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hs : letI := s.toRingHom.toAlgebra;Module.Flat A B)
    (J : Ideal A) (hkill : RingHom.ker (orbitTargetHom s t x)*J=⊥) :
    letI := orbitAlgebra s x
    Ideal.map s.toRingHom J ≃ₗ[K] orbit s x ⊗[K] J := by
  letI := orbitAlgebra s x
  letI := s.toRingHom.toAlgebra
  letI := (orbitTargetHom s t x).toAlgebra
  letI := hs
  letI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq (fun k=>(s.commutes k).symm)
  letI : IsScalarTower K A (orbit s x) := IsScalarTower.of_algebraMap_eq (fun k=>((orbitTarget s t x).commutes k).symm)
  letI := FourCorner.ModuleSurjectiveScalars.idealLayerModule (orbitTargetHom s t x) (orbitTarget_surjective s t x hgen) J hkill
  letI : IsScalarTower A (orbit s x) J := FourCorner.ModuleSurjectiveScalars.idealLayerModule_tower (orbitTargetHom s t x) (orbitTarget_surjective s t x hgen) J hkill
  letI : IsScalarTower K (orbit s x) J := FourCorner.ModuleSurjectiveScalars.idealLayerModule_base_tower (orbitTarget s t x) (orbitTarget_surjective s t x hgen) J hkill
  exact FourCorner.RelativeTensorCancel.idealCoordinates K A (orbit s x) B J (orbitTensorPairEquiv s t x hgen heq)

 def idealSourceMap (s : A →ₐ[K] B) (J : Ideal A) : J →ₗ[K] Ideal.map s.toRingHom J where
  toFun j := ⟨s (j : A),Ideal.mem_map_of_mem _ j.property⟩
  map_add' j k := by apply Subtype.ext;exact map_add s _ _
  map_smul' k j := by apply Subtype.ext;exact map_smul s k (j : A)

 def idealTargetMap (s t : A →ₐ[K] B) (J : Ideal A) (hstable : Ideal.map s.toRingHom J=Ideal.map t.toRingHom J) :
    J →ₗ[K] Ideal.map s.toRingHom J where
  toFun j := ⟨t (j : A),hstable.symm ▸ Ideal.mem_map_of_mem t.toRingHom j.property⟩
  map_add' j k := by apply Subtype.ext;exact map_add t _ _
  map_smul' k j := by apply Subtype.ext;exact map_smul t k (j : A)

 theorem orbitIdealCoordinates_source (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hs : letI := s.toRingHom.toAlgebra;Module.Flat A B)
    (J : Ideal A) (hkill : RingHom.ker (orbitTargetHom s t x)*J=⊥) (j : J) :
    letI := orbitAlgebra s x
    orbitIdealCoordinates s t x hgen heq hs J hkill (idealSourceMap s J j)=(1 : orbit s x) ⊗ₜ[K] j := by
  letI := orbitAlgebra s x
  letI := s.toRingHom.toAlgebra
  letI := (orbitTargetHom s t x).toAlgebra
  letI := hs
  letI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq (fun k=>(s.commutes k).symm)
  letI : IsScalarTower K A (orbit s x) := IsScalarTower.of_algebraMap_eq (fun k=>((orbitTarget s t x).commutes k).symm)
  letI := FourCorner.ModuleSurjectiveScalars.idealLayerModule (orbitTargetHom s t x) (orbitTarget_surjective s t x hgen) J hkill
  letI : IsScalarTower A (orbit s x) J := FourCorner.ModuleSurjectiveScalars.idealLayerModule_tower (orbitTargetHom s t x) (orbitTarget_surjective s t x hgen) J hkill
  letI : IsScalarTower K (orbit s x) J := FourCorner.ModuleSurjectiveScalars.idealLayerModule_base_tower (orbitTarget s t x) (orbitTarget_surjective s t x hgen) J hkill
  exact FourCorner.RelativeTensorCancel.idealCoordinates_source K A (orbit s x) B J (orbitTensorPairEquiv s t x hgen heq) j

/-- ACTUAL original ideal-layer map rho. It is built from original t(j)
in the SAME J·B⊂B, then through the true coordinates; no descent datum or
coaction equation is assumed to define it. -/
def orbitIdealRho (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hs : letI := s.toRingHom.toAlgebra;Module.Flat A B)
    (J : Ideal A) (hkill : RingHom.ker (orbitTargetHom s t x)*J=⊥)
    (hstable : Ideal.map s.toRingHom J=Ideal.map t.toRingHom J) :
    letI := orbitAlgebra s x
    J →ₗ[K] orbit s x ⊗[K] J := by
  letI := orbitAlgebra s x
  exact (orbitIdealCoordinates s t x hgen heq hs J hkill).toLinearMap.comp (idealTargetMap s t J hstable)

/-- Essential original-ring guard: rho-invariance is equivalent to the
literal s(j)=t(j) IN B, not merely modulo I·B. -/
theorem orbitIdealRho_invariant_iff (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hs : letI := s.toRingHom.toAlgebra;Module.Flat A B)
    (J : Ideal A) (hkill : RingHom.ker (orbitTargetHom s t x)*J=⊥)
    (hstable : Ideal.map s.toRingHom J=Ideal.map t.toRingHom J) (j : J) :
    letI := orbitAlgebra s x
    orbitIdealRho s t x hgen heq hs J hkill hstable j=(1 : orbit s x) ⊗ₜ[K] j ↔ s (j : A)=t (j : A) := by
  letI := orbitAlgebra s x
  rw [← orbitIdealCoordinates_source s t x hgen heq hs J hkill j]
  change orbitIdealCoordinates s t x hgen heq hs J hkill (idealTargetMap s t J hstable j)=
    orbitIdealCoordinates s t x hgen heq hs J hkill (idealSourceMap s J j) ↔ _
  constructor
  · intro h
    exact (congrArg Subtype.val ((orbitIdealCoordinates s t x hgen heq hs J hkill).injective h)).symm
  · intro h
    apply congrArg (orbitIdealCoordinates s t x hgen heq hs J hkill)
    exact Subtype.ext h.symm

 theorem orbitIdealRho_injective (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (hs : letI := s.toRingHom.toAlgebra;Module.Flat A B)
    (J : Ideal A) (hkill : RingHom.ker (orbitTargetHom s t x)*J=⊥)
    (hstable : Ideal.map s.toRingHom J=Ideal.map t.toRingHom J) :
    Function.Injective (orbitIdealRho s t x hgen heq hs J hkill hstable) := by
  letI := orbitAlgebra s x
  have htinj : Function.Injective t := Function.LeftInverse.injective
    (fun a=>RingHom.congr_fun (diagonal_target s.toRingHom t.toRingHom heq) a)
  intro j k h
  apply Subtype.ext
  apply htinj
  exact congrArg Subtype.val ((orbitIdealCoordinates s t x hgen heq hs J hkill).injective h)

#print axioms orbitIdealCoordinates
#print axioms orbitIdealRho
#print axioms orbitIdealRho_invariant_iff
#print axioms orbitIdealRho_injective
end
end FourCorner.FiniteRelationOrbit
