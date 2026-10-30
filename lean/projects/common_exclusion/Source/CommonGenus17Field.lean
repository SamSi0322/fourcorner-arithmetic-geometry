import CommonFifthDegree

noncomputable section
namespace FourCorner.CommonGenus17Field
open IntermediateField
variable (K : Type*) [Field K] [CharZero K]

/-- The actual radicand ell/κ in the original four-root field. -/
def radicand (t κ : K) : CommonLiteralField.field K t :=
  algebraMap (RatFunc K) (CommonLiteralField.field K t)
    (RatFunc.X / algebraMap K (RatFunc K) κ)

theorem radicand_nonsquare {t κ : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm : t ≠ -1) (hκ : κ ≠ 0) : ¬ IsSquare (radicand K t κ) := by
  have h := CommonFifthDegree.fifth_nonsquare_of_products
    (CommonFiveIndependence.value t κ) (CommonLiteralField.radical K t)
    (fun i => by simpa only [CommonFiveIndependence.value_castSucc] using
      CommonLiteralField.radical_sq K t i)
    (by norm_num : (2 : RatFunc K) ≠ 0)
    (CommonFiveIndependence.nonempty_product_nonsquare ht0 ht1 htm hκ)
  have he : Set.range (CommonLiteralField.radical K t) =
      {CommonLiteralField.radical K t 0,CommonLiteralField.radical K t 1,
       CommonLiteralField.radical K t 2,CommonLiteralField.radical K t 3} := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
      · exact ⟨3,rfl⟩
  unfold radicand CommonLiteralField.field
  rw [he]
  exact h

def radical (t κ : K) : AlgebraicClosure (CommonLiteralField.field K t) :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (CommonLiteralField.field K t)
      (AlgebraicClosure (CommonLiteralField.field K t)) (radicand K t κ))
    (show 0 < (2 : ℕ) by decide))

theorem radical_sq (t κ : K) : radical K t κ ^ 2 =
    algebraMap (CommonLiteralField.field K t)
      (AlgebraicClosure (CommonLiteralField.field K t)) (radicand K t κ) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (CommonLiteralField.field K t)
      (AlgebraicClosure (CommonLiteralField.field K t)) (radicand K t κ))
    (show 0 < (2 : ℕ) by decide))

/-- Literal extension adjoining sqrt(ell/κ) to the original common field. -/
def field (t κ : K) : IntermediateField (CommonLiteralField.field K t)
    (AlgebraicClosure (CommonLiteralField.field K t)) :=
  IntermediateField.adjoin (CommonLiteralField.field K t) {radical K t κ}

theorem finrank_eq_two {t κ : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm : t ≠ -1) (hκ : κ ≠ 0) :
    Module.finrank (CommonLiteralField.field K t) (field K t κ) = 2 := by
  apply Multiquadratic.finrank_adjoin_square_root _ (radical_sq K t κ)
  intro x hx
  apply radicand_nonsquare K ht0 ht1 htm hκ
  exact ⟨x, by simpa only [sq] using hx.symm⟩

#print axioms radicand_nonsquare
#print axioms finrank_eq_two
end FourCorner.CommonGenus17Field
