import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Tactic

noncomputable section
namespace FourCorner.CommonTensorRank
open scoped TensorProduct

/-- A surjective map between equal-dimensional finite algebras into a field
makes the source a domain. This is applied to genuine scalar tensor products,
with both dimensions independently calculated from squareclass independence. -/
theorem tensor_isDomain_of_surjective_same_finrank
    (F G E J : Type*) [Field F] [Field G] [Field E] [Field J]
    [Algebra F G] [Algebra F E] [Algebra G J] [Algebra F J]
    [IsScalarTower F G J] [FiniteDimensional F E]
    (f : E →ₐ[F] J)
    (hsurj : Function.Surjective
      (Algebra.TensorProduct.lift (Algebra.ofId G J) f
        (fun _ _ => Commute.all _ _) : G ⊗[F] E →ₐ[G] J))
    (hdim : Module.finrank G J = Module.finrank F E) :
    IsDomain (G ⊗[F] E) := by
  letI : FiniteDimensional G J := FiniteDimensional.of_finrank_pos (by
    rw [hdim]
    exact Module.finrank_pos)
  let φ : G ⊗[F] E →ₐ[G] J := Algebra.TensorProduct.lift (Algebra.ofId G J) f
    (fun _ _ => Commute.all _ _)
  have hd : Module.finrank G (G ⊗[F] E) = Module.finrank G J := by
    rw [Module.finrank_baseChange,hdim]
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hsurj
  exact Function.Injective.isDomain φ hinj

#print axioms tensor_isDomain_of_surjective_same_finrank
end FourCorner.CommonTensorRank

noncomputable section
namespace FourCorner.CommonTensorRank
open scoped TensorProduct
variable {F G E C : Type*} [Field F] [Field G] [Field E] [Field C]
  [Algebra F G] [Algebra F E] [Algebra G C] [Algebra F C] [IsScalarTower F G C]

/-- Images of algebra generators land in their actual generated field. -/
theorem map_mem_adjoin (f : E →ₐ[F] C) (r : Fin 4 → E)
    (hgen : Algebra.adjoin F (Set.range r) = ⊤) (x : E) :
    f x ∈ IntermediateField.adjoin G (Set.range (fun i => f (r i))) := by
  let J := IntermediateField.adjoin G (Set.range (fun i => f (r i)))
  have h : Algebra.adjoin F (Set.range r) ≤
      ((J.toSubalgebra.restrictScalars F).comap f) := by
    apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    exact IntermediateField.subset_adjoin G _ ⟨i,rfl⟩
  rw [hgen] at h
  exact h (show x ∈ (⊤ : Subalgebra F E) by trivial)

def imageHom (f : E →ₐ[F] C) (r : Fin 4 → E)
    (hgen : Algebra.adjoin F (Set.range r) = ⊤) :
    E →ₐ[F] IntermediateField.adjoin G (Set.range (fun i => f (r i))) :=
  f.codRestrict
    ((IntermediateField.adjoin G (Set.range (fun i => f (r i)))).toSubalgebra.restrictScalars F)
    (map_mem_adjoin (G:=G) f r hgen)

theorem tensor_lift_surjective (f : E →ₐ[F] C) (r : Fin 4 → E)
    (hgen : Algebra.adjoin F (Set.range r) = ⊤)
    (halg : ∀ i, IsAlgebraic G (f (r i))) :
    Function.Surjective
      (Algebra.TensorProduct.lift (Algebra.ofId G _)
        (imageHom (G:=G) f r hgen) (fun _ _ => Commute.all _ _)) := by
  let J := IntermediateField.adjoin G (Set.range (fun i => f (r i)))
  let φ : G ⊗[F] E →ₐ[G] J := Algebra.TensorProduct.lift (Algebra.ofId G J)
    (imageHom (G:=G) f r hgen) (fun _ _ => Commute.all _ _)
  have hgenJ : Algebra.adjoin G (Set.range (fun i => (imageHom (G:=G) f r hgen) (r i))) = ⊤ := by
    apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic ?_).mp
    · apply IntermediateField.lift_injective J
      rw [IntermediateField.lift_adjoin,IntermediateField.lift_top]
      congr 1
      ext x
      simp only [Set.mem_image,Set.mem_range]
      constructor
      · rintro ⟨_,⟨i,rfl⟩,rfl⟩
        exact ⟨i,rfl⟩
      · rintro ⟨i,rfl⟩
        exact ⟨(imageHom (G:=G) f r hgen) (r i),⟨i,rfl⟩,rfl⟩
    · rintro _ ⟨i,rfl⟩
      exact (isAlgebraic_algHom_iff J.val J.val.injective).mp (halg i)
  have htop : φ.range = ⊤ := by
    apply top_unique
    rw [← hgenJ]
    apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    exact ⟨1 ⊗ₜ[F] r i,by
      change φ (1 ⊗ₜ[F] r i) = _
      simp only [φ,Algebra.TensorProduct.lift_tmul,map_one,one_mul]⟩
  intro x
  have hx : x ∈ φ.range := by rw [htop]; trivial
  exact hx

#print axioms tensor_lift_surjective
end FourCorner.CommonTensorRank
