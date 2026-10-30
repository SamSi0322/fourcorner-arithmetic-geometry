import ThetaCoverClassPortable.ModuleSurjectiveScalars

namespace FourCorner.ModuleSurjectiveScalars
noncomputable section
universe u v w
variable {A : Type u} [CommRing A] {D : Type v} [CommRing D]

 theorem kernel_annihilates_ideal (o : A →+* D) (J : Ideal A)
    (hJ : RingHom.ker o*J=⊥) :
    ∀a∈RingHom.ker o,∀j : J,a • j=0 := by
  intro a ha j
  apply Subtype.ext
  change a*(j : A)=0
  exact (show a*(j : A)∈(⊥ : Ideal A) from hJ ▸ Ideal.mul_mem_mul ha j.property)

 theorem idealLayerModule_tower (o : A →+* D) (ho : Function.Surjective o)
    (J : Ideal A) (hJ : RingHom.ker o*J=⊥) :
    letI := o.toAlgebra
    letI := idealLayerModule o ho J hJ
    IsScalarTower A D J := by
  exact descendedModule_tower o ho (kernel_annihilates_ideal o J hJ)

 theorem idealLayerModule_base_tower {K : Type w} [CommRing K] [Algebra K A] [Algebra K D]
    (o : A →ₐ[K] D) (ho : Function.Surjective o)
    (J : Ideal A) (hJ : RingHom.ker o.toRingHom*J=⊥) :
    letI := idealLayerModule o.toRingHom ho J hJ
    IsScalarTower K D J := by
  exact descendedModule_base_tower o ho (kernel_annihilates_ideal o.toRingHom J hJ)

#print axioms idealLayerModule_tower
#print axioms idealLayerModule_base_tower
end
end FourCorner.ModuleSurjectiveScalars
