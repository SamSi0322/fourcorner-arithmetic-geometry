import CommonFieldTensorDomain

noncomputable section
namespace FourCorner.CommonRootFieldComparison
open scoped TensorProduct
open CommonLiteralField

theorem adjoin_eq_of_equal_squares {F C : Type*} [Field F] [Field C] [Algebra F C]
    {ι : Type*} (r s : ι → C) (hsq : ∀ i, r i ^ 2 = s i ^ 2) :
    IntermediateField.adjoin F (Set.range r) = IntermediateField.adjoin F (Set.range s) := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq i) with hh | hh
    · rw [hh]; exact IntermediateField.subset_adjoin F _ ⟨i,rfl⟩
    · rw [hh]; exact IntermediateField.neg_mem _ (IntermediateField.subset_adjoin F _ ⟨i,rfl⟩)
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq i).symm with hh | hh
    · rw [hh]; exact IntermediateField.subset_adjoin F _ ⟨i,rfl⟩
    · rw [hh]; exact IntermediateField.neg_mem _ (IntermediateField.subset_adjoin F _ ⟨i,rfl⟩)

variable (K L : Type*) [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]

/-- Actual scalar extension over the rational-function base is the literal
four-root field over the new constants, up to a constructed algebra equivalence.
The arbitrary choices of square roots differ only by signs. -/
def baseChangeEquiv {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    letI := CommonFieldTensorDomain.ratAlgebra K L
    (RatFunc L) ⊗[RatFunc K] (field K t) ≃ₐ[RatFunc L]
      field L (algebraMap K L t) := by
  letI := CommonFieldTensorDomain.ratAlgebra K L
  let F := RatFunc K
  let G := RatFunc L
  let E := field K t
  let C := AlgebraicClosure G
  letI : FiniteDimensional F E := FiniteDimensional.of_finrank_pos (by
    rw [finrank_field_eq_sixteen K ht0 ht1 htm]; norm_num)
  let f : E →ₐ[F] C := IsAlgClosed.lift
  let r : Fin 4 → E := root K t
  let q : Fin 4 → G := radicand L (algebraMap K L t)
  have hr (i : Fin 4) : f (r i)^2 = algebraMap G C (q i) := by
    rw [← map_pow]
    change f (root K t i ^ 2) = _
    rw [root_sq,AlgHom.commutes,IsScalarTower.algebraMap_apply F G C]
    change algebraMap G C (CommonConstantMap.ratMap K L (radicand K t i)) = _
    rw [CommonConstantMap.radicand_map]
  have hgen : Algebra.adjoin F (Set.range r) = ⊤ := by
    have he : Set.range r = {r 0,r 1,r 2,r 3} := by
      ext x
      simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,rfl⟩; fin_cases i <;> tauto
      · intro hx
        rcases hx with hx | hx | hx | hx
        · exact ⟨0,hx.symm⟩
        · exact ⟨1,hx.symm⟩
        · exact ⟨2,hx.symm⟩
        · exact ⟨3,hx.symm⟩
    rw [he]
    exact root_generates t
  have halg (i : Fin 4) : IsAlgebraic G (f (r i)) := by
    have hi : IsIntegral G (f (r i)) := by
      refine ⟨Polynomial.X^2-Polynomial.C (q i),Polynomial.monic_X_pow_sub_C _ (by decide),?_⟩
      simp [hr i]
    exact hi.isAlgebraic
  let J := IntermediateField.adjoin G (Set.range (fun i => f (r i)))
  have hJ : J = field L (algebraMap K L t) := by
    apply adjoin_eq_of_equal_squares
    intro i
    exact (hr i).trans (radical_sq L (algebraMap K L t) i).symm
  let φ : G ⊗[F] E →ₐ[G] J := Algebra.TensorProduct.lift (Algebra.ofId G J)
    (CommonTensorRank.imageHom (G:=G) f r hgen) (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective φ :=
    CommonTensorRank.tensor_lift_surjective (G:=G) f r hgen halg
  have hdim : Module.finrank G J = Module.finrank F E := by
    have hd := (IntermediateField.equivOfEq hJ).toLinearEquiv.finrank_eq
    rw [finrank_field_eq_sixteen L ((map_ne_zero _).mpr ht0)
      (by simpa only [map_one] using (algebraMap K L).injective.ne ht1)
      (by simpa only [map_neg,map_one] using (algebraMap K L).injective.ne htm)] at hd
    rw [finrank_field_eq_sixteen K ht0 ht1 htm]
    exact hd
  letI : FiniteDimensional G J := FiniteDimensional.of_finrank_pos (by rw [hdim]; exact Module.finrank_pos)
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_baseChange,hdim])).mpr hsurj
  exact (AlgEquiv.ofBijective φ ⟨hinj,hsurj⟩).trans (IntermediateField.equivOfEq hJ)

#print axioms adjoin_eq_of_equal_squares
#print axioms baseChangeEquiv
end FourCorner.CommonRootFieldComparison
