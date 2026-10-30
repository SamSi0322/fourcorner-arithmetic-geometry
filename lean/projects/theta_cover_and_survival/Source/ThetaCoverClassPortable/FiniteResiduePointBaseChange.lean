import ThetaCoverClassPortable.StableIdealNilpotence

namespace FourCorner.FiniteResiduePointBaseChange
noncomputable section
open scoped TensorProduct
universe u

/-- A real finite residue extension supplies a real rational point on the
FULL scalar-changed algebra, preserving its full dimension and all its
nilpotents. No algebraic closure or field-point substitution is used. -/
theorem exists_finite_pointed_baseChange (K A : Type u) [Field K] [CommRing A]
    [Algebra K A] [Nontrivial A] [Module.Finite K A] :
    ∃(L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (x : L ⊗[K] A →ₐ[L] L),Module.finrank L (L ⊗[K] A)=Module.finrank K A := by
  obtain ⟨m,hm⟩ := Ideal.exists_maximal A
  letI := hm
  let L := A ⧸ m
  letI : Field L := Ideal.Quotient.field m
  letI : Algebra K L := inferInstance
  letI : Module.Finite K L := Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
    (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk m))
  let x : L ⊗[K] A →ₐ[L] L :=
    Algebra.TensorProduct.lift (AlgHom.id L L) (Ideal.Quotient.mkₐ K m) (fun _ _=>Commute.all _ _)
  exact ⟨L,inferInstance,inferInstance,inferInstance,x,Module.finrank_baseChange⟩

#print axioms exists_finite_pointed_baseChange
end
end FourCorner.FiniteResiduePointBaseChange
