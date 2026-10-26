import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
namespace FourCorner.FractionFieldGenerators
variable {k A F ι : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Algebra k F] [IsScalarTower k A F]

/-- Literal affine-ring generators generate its actual fraction field as
an intermediate FIELD, without a finite-type or characteristic assumption. -/
theorem adjoin_eq_top (r : ι → A) (h : Algebra.adjoin k (Set.range r)=⊤) :
    IntermediateField.adjoin k (Set.range (fun i => algebraMap A F (r i)))=⊤ := by
  let S := IntermediateField.adjoin k (Set.range (fun i => algebraMap A F (r i)))
  have hA : ∀ a : A, algebraMap A F a ∈ S := by
    have hs : Algebra.adjoin k (Set.range r) ≤
        S.toSubalgebra.comap (IsScalarTower.toAlgHom k A F) := by
      apply Algebra.adjoin_le
      rintro _ ⟨i,rfl⟩
      exact IntermediateField.subset_adjoin k _ ⟨i,rfl⟩
    rw [h] at hs
    exact fun a => hs (show a ∈ (⊤ : Subalgebra k A) by trivial)
  apply top_unique
  intro z _
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective A z
  exact S.div_mem (hA a) (hA b)

end FourCorner.FractionFieldGenerators
#print axioms FourCorner.FractionFieldGenerators.adjoin_eq_top
