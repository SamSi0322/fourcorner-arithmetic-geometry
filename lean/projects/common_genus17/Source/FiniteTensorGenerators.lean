import CommonTensorRank

/-! Generic-index version of the project's existing CommonTensorRank generator
lemmas. The original four-root proofs are unchanged in the canonical parent. -/
noncomputable section
namespace FourCorner.FiniteTensorGenerators
open scoped TensorProduct
variable {F G E C : Type*} [Field F] [Field G] [Field E] [Field C]
  [Algebra F G] [Algebra F E] [Algebra G C] [Algebra F C] [IsScalarTower F G C]

/-- Images of algebra generators land in their actual generated field. -/
theorem map_mem_adjoin (f : E →ₐ[F] C) {ι : Type*} (r : ι → E)
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

def imageHom (f : E →ₐ[F] C) {ι : Type*} (r : ι → E)
    (hgen : Algebra.adjoin F (Set.range r) = ⊤) :
    E →ₐ[F] IntermediateField.adjoin G (Set.range (fun i => f (r i))) :=
  f.codRestrict
    ((IntermediateField.adjoin G (Set.range (fun i => f (r i)))).toSubalgebra.restrictScalars F)
    (map_mem_adjoin (G:=G) f r hgen)

theorem tensor_lift_surjective (f : E →ₐ[F] C) {ι : Type*} (r : ι → E)
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
end FourCorner.FiniteTensorGenerators
