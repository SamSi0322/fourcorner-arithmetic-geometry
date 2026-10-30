import CommonActualGenus
import CommonConstantMap
import CommonTensorRank

noncomputable section
namespace FourCorner.CommonFieldTensorDomain
open scoped TensorProduct
open CommonLiteralField
variable (K L : Type*) [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]

def ratAlgebra : Algebra (RatFunc K) (RatFunc L) :=
  (CommonConstantMap.ratMap K L).toAlgebra

/-- Extending the rational-function base of the actual four-root field to
L(ell) gives a genuine domain, since the four squareclasses remain independent. -/
theorem isDomain_rationalFunction_baseChange {t : K}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    letI := ratAlgebra K L
    IsDomain ((RatFunc L) ⊗[RatFunc K] (CommonLiteralField.field K t)) := by
  letI := ratAlgebra K L
  let F := RatFunc K
  let G := RatFunc L
  let E := CommonLiteralField.field K t
  let C := AlgebraicClosure G
  letI : FiniteDimensional F E := FiniteDimensional.of_finrank_pos (by
    rw [finrank_field_eq_sixteen K ht0 ht1 htm]; norm_num)
  let f : E →ₐ[F] C := IsAlgClosed.lift
  let r : Fin 4 → E := CommonLiteralField.root K t
  let q : Fin 4 → G := CommonLiteralField.radicand L (algebraMap K L t)
  have hr (i : Fin 4) : f (r i)^2 = algebraMap G C (q i) := by
    rw [← map_pow]
    change f (CommonLiteralField.root K t i ^ 2) = _
    rw [root_sq,AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply F G C]
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
  have ht0' : algebraMap K L t ≠ 0 := (map_ne_zero _).mpr ht0
  have ht1' : algebraMap K L t ≠ 1 := by
    simpa only [map_one] using (algebraMap K L).injective.ne ht1
  have htm' : algebraMap K L t ≠ -1 := by
    simpa only [map_neg,map_one] using (algebraMap K L).injective.ne htm
  have hdimJ : Module.finrank G J = 16 := by
    have he : Set.range (fun i => f (r i)) = {f (r 0),f (r 1),f (r 2),f (r 3)} := by
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
    have heJ : J = IntermediateField.adjoin G {f (r 0),f (r 1),f (r 2),f (r 3)} :=
      congrArg (IntermediateField.adjoin G) he
    have hdeg := CommonFourDegree.finrank_four_eq_sixteen_of_products q (fun i => f (r i)) hr
      (by norm_num) (CommonFiveIndependence.four_product_nonsquare ht0' ht1' htm')
    exact (IntermediateField.equivOfEq heJ).toLinearEquiv.finrank_eq.trans hdeg
  apply CommonTensorRank.tensor_isDomain_of_surjective_same_finrank F G E J
    (CommonTensorRank.imageHom (G:=G) f r hgen)
    (CommonTensorRank.tensor_lift_surjective (G:=G) f r hgen halg)
  rw [hdimJ]
  exact (finrank_field_eq_sixteen K ht0 ht1 htm).symm

#print axioms isDomain_rationalFunction_baseChange
end FourCorner.CommonFieldTensorDomain
