import ThetaCoverClassPortable.FiniteRelationOrbitIdeal

namespace FourCorner.ModuleSurjectiveScalars
noncomputable section
universe u v w
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]
variable {M : Type w} [AddCommGroup M] [Module R M]

 def descendedSMul (f : R →+* S) (hf : Function.Surjective f) : SMul S M :=
  ⟨fun s m=>(hf s).choose • m⟩

 theorem descended_smul (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀a∈RingHom.ker f,∀m : M,a • m=0) (a : R) (m : M) :
    letI := descendedSMul (M:=M) f hf
    f a • m=a • m := by
  letI := descendedSMul (M:=M) f hf
  change (hf (f a)).choose • m=a • m
  apply sub_eq_zero.mp
  rw [← sub_smul]
  apply hker
  change f ((hf (f a)).choose-a)=0
  rw [map_sub,(hf (f a)).choose_spec,sub_self]

/-- Actual descended module action through a surjective scalar hom,
constructed from the genuine kernel-annihilation proof. -/
def descendedModule (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀a∈RingHom.ker f,∀m : M,a • m=0) : Module S M := by
  letI := descendedSMul (M:=M) f hf
  exact hf.moduleLeft f (descended_smul f hf hker)

 theorem descendedModule_smul (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀a∈RingHom.ker f,∀m : M,a • m=0) (a : R) (m : M) :
    letI := descendedModule f hf hker
    f a • m=a • m :=
  descended_smul f hf hker a m

 theorem descendedModule_tower (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀a∈RingHom.ker f,∀m : M,a • m=0) :
    letI := f.toAlgebra
    letI := descendedModule f hf hker
    IsScalarTower R S M := by
  letI := f.toAlgebra
  letI := descendedModule f hf hker
  constructor
  intro r s m
  change (f r*s) • m=r • (s • m)
  rw [mul_smul,descendedModule_smul]

 theorem descendedModule_base_tower {K : Type*} [CommRing K] [Algebra K R] [Algebra K S]
    [Module K M] [IsScalarTower K R M]
    (f : R →ₐ[K] S) (hf : Function.Surjective f)
    (hker : ∀a∈RingHom.ker f.toRingHom,∀m : M,a • m=0) :
    letI := descendedModule f.toRingHom hf hker
    IsScalarTower K S M := by
  letI := descendedModule f.toRingHom hf hker
  apply IsScalarTower.of_algebraMap_smul
  intro k m
  rw [← f.commutes]
  exact (descendedModule_smul f.toRingHom hf hker (algebraMap K R k) m).trans
    (IsScalarTower.algebraMap_smul R k m)

/-- Apply the construction to a true stable-ideal layer J killed by the
orbit kernel I. This is the ACTUAL J, not an abstract replacement module. -/
def idealLayerModule {A D : Type*} [CommRing A] [CommRing D]
    (o : A →+* D) (ho : Function.Surjective o) (J : Ideal A)
    (hJ : RingHom.ker o*J=⊥) : Module D J := by
  apply descendedModule o ho
  intro a ha j
  apply Subtype.ext
  change a*(j : A)=0
  exact (show a*(j : A)∈(⊥ : Ideal A) from hJ ▸ Ideal.mul_mem_mul ha j.property)

#print axioms descendedModule
#print axioms descendedModule_tower
#print axioms descendedModule_base_tower
#print axioms idealLayerModule
end
end FourCorner.ModuleSurjectiveScalars
