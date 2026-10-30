import ThetaCoverClassPortable.ModuleSurjectiveScalars

namespace FourCorner.ModuleSurjectiveScalars
noncomputable section
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]
variable {M : Type w} [AddCommGroup M] [Module R M]

 def scalarTensorEval (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀a∈RingHom.ker f,∀m : M,a • m=0) :
    letI := f.toAlgebra
    letI := descendedModule f hf hker
    letI := descendedModule_tower f hf hker
    S ⊗[R] M →ₗ[S] M := by
  letI := f.toAlgebra
  letI := descendedModule f hf hker
  letI := descendedModule_tower f hf hker
  exact TensorProduct.AlgebraTensorModule.lift
    (LinearMap.mk₂' S R (fun s m=>s • m) add_smul (fun c s m=>mul_smul c s m)
      smul_add (fun r s m=>smul_comm s r m))

 def scalarTensorInsert (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀a∈RingHom.ker f,∀m : M,a • m=0) :
    letI := f.toAlgebra
    letI := descendedModule f hf hker
    letI := descendedModule_tower f hf hker
    M →ₗ[S] S ⊗[R] M := by
  letI := f.toAlgebra
  letI := descendedModule f hf hker
  letI := descendedModule_tower f hf hker
  refine {toFun:=fun m=>(1 : S) ⊗ₜ[R] m,map_add':=fun _ _=>TensorProduct.tmul_add _ _ _,map_smul':=?_}
  intro s m
  obtain ⟨r,rfl⟩ := hf s
  rw [descendedModule_smul]
  exact (TensorProduct.tmul_smul r (1 : S) m).trans
    (IsScalarTower.algebraMap_smul S r ((1 : S) ⊗ₜ[R] m)).symm

/-- Actual annihilated module is recovered after tensoring through the
surjective quotient. Both maps and both inverse identities are proved. -/
def scalarTensorEquiv (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀a∈RingHom.ker f,∀m : M,a • m=0) :
    letI := f.toAlgebra
    letI := descendedModule f hf hker
    letI := descendedModule_tower f hf hker
    S ⊗[R] M ≃ₗ[S] M := by
  letI := f.toAlgebra
  letI := descendedModule f hf hker
  letI := descendedModule_tower f hf hker
  apply LinearEquiv.ofLinearMap (scalarTensorEval f hf hker) (scalarTensorInsert f hf hker)
  · apply LinearMap.ext
    intro m
    change (1 : S) • m=m
    exact one_smul S m
  · apply TensorProduct.AlgebraTensorModule.ext
    intro s m
    change scalarTensorInsert f hf hker (s • m)=s ⊗ₜ[R] m
    rw [map_smul]
    change s • ((1 : S) ⊗ₜ[R] m)=s ⊗ₜ[R] m
    rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]

#print axioms scalarTensorInsert
#print axioms scalarTensorEquiv
end
end FourCorner.ModuleSurjectiveScalars
