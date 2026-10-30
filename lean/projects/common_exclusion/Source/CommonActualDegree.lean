import CommonLiteralField
import CommonFourDegree
import CommonFiveIndependence

noncomputable section
namespace FourCorner.CommonLiteralField
variable (K : Type*) [Field K] [CharZero K]

/-- The literal common four-root function field has actual degree sixteen,
for precisely the paper's nondegenerate parameter range. -/
theorem finrank_field_eq_sixteen {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm : t ≠ -1) : Module.finrank (RatFunc K) (field K t) = 16 := by
  have h := CommonFourDegree.finrank_four_eq_sixteen_of_products
    (radicand K t) (radical K t) (radical_sq K t) (by norm_num)
    (CommonFiveIndependence.four_product_nonsquare ht0 ht1 htm)
  have hs : Set.range (radical K t) =
      {radical K t 0, radical K t 1, radical K t 2, radical K t 3} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> tauto
    · intro hx
      rcases hx with hx | hx | hx | hx
      · exact ⟨0,hx.symm⟩
      · exact ⟨1,hx.symm⟩
      · exact ⟨2,hx.symm⟩
      · exact ⟨3,hx.symm⟩
  change Module.finrank (RatFunc K) (IntermediateField.adjoin (RatFunc K) (Set.range (radical K t))) = 16
  rw [hs]
  exact h

#print axioms finrank_field_eq_sixteen
end FourCorner.CommonLiteralField
