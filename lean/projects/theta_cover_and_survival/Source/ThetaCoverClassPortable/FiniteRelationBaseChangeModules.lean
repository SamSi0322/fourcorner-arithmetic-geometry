import ThetaCoverClassPortable.FiniteRelationRingBaseChange
import ThetaCoverClassPortable.ProjectiveTraceRank
import Mathlib.RingTheory.RingHom.Flat

namespace FourCorner.FiniteRelationRingBaseChange
open FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
open scoped TensorProduct
universe u
variable {C A B S : Type u} [CommRing C] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra C A] [Algebra C B] [Algebra C S]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- ACTUAL module/algebra base-change identification for the original
source map after arbitrary C-scalar extension, no flatness of S/C. -/
def changeMap_baseChangeEquiv (f : A →ₐ[C] B) :
    letI := f.toRingHom.toAlgebra
    letI : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq (fun c=>(f.commutes c).symm)
    letI := (changeMap (S:=S) f).toRingHom.toAlgebra
    S ⊗[C] B ≃ₐ[S ⊗[C] A] (S ⊗[C] A) ⊗[A] B := by
  letI := f.toRingHom.toAlgebra
  letI : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq (fun c=>(f.commutes c).symm)
  letI := (changeMap (S:=S) f).toRingHom.toAlgebra
  exact
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg C S A (S ⊗[C] A) B).symm
      commutes' := fun x=>congrArg (fun g=>g x) (Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor C A B S) }

 theorem changeMap_finite_projective (f : A →ₐ[C] B)
    (hf : letI := f.toRingHom.toAlgebra;Module.Finite A B)
    (hp : letI := f.toRingHom.toAlgebra;Module.Projective A B) :
    letI := (changeMap (S:=S) f).toRingHom.toAlgebra
    Module.Finite (S ⊗[C] A) (S ⊗[C] B) ∧ Module.Projective (S ⊗[C] A) (S ⊗[C] B) := by
  letI := f.toRingHom.toAlgebra
  letI := hf
  letI := hp
  letI : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq (fun c=>(f.commutes c).symm)
  letI := (changeMap (S:=S) f).toRingHom.toAlgebra
  letI := projective_tensor (R:=A) (M:=B) (S ⊗[C] A)
  let e := changeMap_baseChangeEquiv (S:=S) f
  exact ⟨Module.Finite.equiv e.symm.toLinearEquiv,Module.Projective.of_equiv e.symm.toLinearEquiv⟩

 theorem changeMap_flat (f : A →ₐ[C] B) (hf : f.toRingHom.Flat) :
    (changeMap (S:=S) f).toRingHom.Flat :=
  RingHom.Flat.tensorProductMap (RingHom.Flat.of_bijective (Function.bijective_id : Function.Bijective (fun x : S=>x))) hf

 theorem changeMap_constant_rank (f : A →ₐ[C] B)
    (hf : letI := f.toRingHom.toAlgebra;Module.Finite A B)
    (hp : letI := f.toRingHom.toAlgebra;Module.Projective A B)
    (n : ℕ) (hr : letI := f.toRingHom.toAlgebra;∀p : PrimeSpectrum A,Module.rankAtStalk B p=n) :
    letI := (changeMap (S:=S) f).toRingHom.toAlgebra
    ∀p : PrimeSpectrum (S ⊗[C] A),Module.rankAtStalk (S ⊗[C] B) p=n := by
  letI := f.toRingHom.toAlgebra
  letI := hf
  letI := hp
  letI : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq (fun c=>(f.commutes c).symm)
  letI := (changeMap (S:=S) f).toRingHom.toAlgebra
  let e := changeMap_baseChangeEquiv (S:=S) f
  intro p
  exact (congrFun (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv) p).trans
    ((Module.rankAtStalk_baseChange (R:=A) (M:=B) (S:=S ⊗[C] A) p).trans (hr _))

#print axioms changeMap_baseChangeEquiv
#print axioms changeMap_finite_projective
#print axioms changeMap_flat
#print axioms changeMap_constant_rank
end
end FourCorner.FiniteRelationRingBaseChange
