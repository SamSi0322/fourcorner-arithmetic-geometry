import ThetaCoverClassPortable.FiniteResiduePointBaseChange

namespace FourCorner.FiniteResiduePointBaseChange
noncomputable section
open scoped TensorProduct
universe u

/-- Actual finite residue extension and actual rational point on the
DIRECT original C-scalar fibre. The dimension comparison is a true
relative tensor-cancellation isomorphism, not a model-identity premise. -/
theorem exists_finite_point_on_direct_scalar_change (C A K : Type u)
    [CommRing C] [CommRing A] [Field K] [Algebra C A] [Algebra C K]
    [Module.Finite C A] [Nontrivial (K ⊗[C] A)] :
    ∃(L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L),
      letI : Algebra C L := ((algebraMap K L).comp (algebraMap C K)).toAlgebra
      ∃x : L ⊗[C] A →ₐ[L] L,Module.finrank L (L ⊗[C] A)=Module.finrank K (K ⊗[C] A) := by
  obtain ⟨L,hField,hAlg,hFinite,x,hDim⟩ := exists_finite_pointed_baseChange K (K ⊗[C] A)
  letI := hField
  letI := hAlg
  letI := hFinite
  letI : Algebra C L := ((algebraMap K L).comp (algebraMap C K)).toAlgebra
  letI : IsScalarTower C K L := IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  let f0 : K ⊗[C] A →ₐ[K] L := (x.restrictScalars K).comp (Algebra.TensorProduct.includeRight : K ⊗[C] A →ₐ[K] L ⊗[K] (K ⊗[C] A))
  let f : A →ₐ[C] L := (f0.restrictScalars C).comp (Algebra.TensorProduct.includeRight : A →ₐ[C] K ⊗[C] A)
  let xC : L ⊗[C] A →ₐ[L] L := Algebra.TensorProduct.lift (AlgHom.id L L) f (fun _ _=>Commute.all _ _)
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange C K L L A
  exact ⟨L,inferInstance,inferInstance,inferInstance,xC,e.finrank_eq.symm.trans hDim⟩

#print axioms exists_finite_point_on_direct_scalar_change
end
end FourCorner.FiniteResiduePointBaseChange
