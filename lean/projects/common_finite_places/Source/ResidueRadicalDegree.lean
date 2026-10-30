import ResidueRadicalField
import FiniteFiveIndependence
import CommonFifthDegree

noncomputable section
namespace FourCorner.ResidueRadicalDegree
open IntermediateField
variable (K : Type*) [Field K] [NeZero (2 : K)]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

theorem two_ratFunc_ne_zero : (2 : RatFunc K) ≠ 0 := by
  simpa only [map_ofNat] using
    (_root_.map_ne_zero (algebraMap K (RatFunc K))).mpr (NeZero.ne (2 : K))

theorem radical_range (t : K) : Set.range (CommonLiteralField.radical K t) =
    {CommonLiteralField.radical K t 0,CommonLiteralField.radical K t 1,
     CommonLiteralField.radical K t 2,CommonLiteralField.radical K t 3} := by
  ext x
  simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> tauto
  · rintro (hx | hx | hx | hx)
    · exact ⟨0,hx.symm⟩
    · exact ⟨1,hx.symm⟩
    · exact ⟨2,hx.symm⟩
    · exact ⟨3,hx.symm⟩

/-- The actual four-root field has degree sixteen in every characteristic !=2. -/
theorem four_degree {t : K} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Module.finrank (RatFunc K) (CommonLiteralField.field K t) = 16 := by
  have h := CommonFourDegree.finrank_four_eq_sixteen_of_products
    (CommonLiteralField.radicand K t) (CommonLiteralField.radical K t)
    (CommonLiteralField.radical_sq K t) (two_ratFunc_ne_zero K)
    (FiniteFiveIndependence.four_product_nonsquare h0 h1 hm)
  change Module.finrank (RatFunc K)
    (IntermediateField.adjoin (RatFunc K) (Set.range (CommonLiteralField.radical K t))) = 16
  rw [radical_range K t]
  exact h

theorem fifth_nonsquare {t κ : K} (h0 : t ≠ 0) (h1 : t ≠ 1)
    (hm : t ≠ -1) (hκ : κ ≠ 0) :
    ¬ IsSquare (CommonGenus17Field.radicand K t κ) := by
  have h := CommonFifthDegree.fifth_nonsquare_of_products
    (CommonFiveIndependence.value t κ) (CommonLiteralField.radical K t)
    (fun i => by simpa only [FiniteFiveIndependence.value_castSucc] using
      CommonLiteralField.radical_sq K t i)
    (two_ratFunc_ne_zero K)
    (FiniteFiveIndependence.nonempty_product_nonsquare h0 h1 hm hκ)
  unfold CommonGenus17Field.radicand CommonLiteralField.field
  rw [radical_range K t]
  exact h

theorem fifth_degree {t κ : K} (h0 : t ≠ 0) (h1 : t ≠ 1)
    (hm : t ≠ -1) (hκ : κ ≠ 0) :
    Module.finrank (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ) = 2 := by
  apply Multiquadratic.finrank_adjoin_square_root _ (ResidueRadicalField.fifth_radical_sq K t κ)
  intro x hx
  exact fifth_nonsquare K h0 h1 hm hκ ⟨x,by simpa only [sq] using hx.symm⟩

/-- Actual degree32 of the literal five-radical residue field; no numerical
degree or geometric genus is assigned in the field definition. -/
theorem degree_thirty_two {t κ : K} (h0 : t ≠ 0) (h1 : t ≠ 1)
    (hm : t ≠ -1) (hκ : κ ≠ 0) :
    Module.finrank (RatFunc K) (CommonGenus17Field.field K t κ) = 32 := by
  letI := ResidueRadicalField.four_finite K t
  letI := ResidueRadicalField.fifth_finite K t κ
  rw [← Module.finrank_mul_finrank (RatFunc K) (CommonLiteralField.field K t)
    (CommonGenus17Field.field K t κ),four_degree K h0 h1 hm,fifth_degree K h0 h1 hm hκ]

end FourCorner.ResidueRadicalDegree
#print axioms FourCorner.ResidueRadicalDegree.fifth_nonsquare
#print axioms FourCorner.ResidueRadicalDegree.degree_thirty_two
