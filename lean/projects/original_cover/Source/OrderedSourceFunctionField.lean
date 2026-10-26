import OrderedSourceRadicands

/-! An independently constructed actual function field for the complete ordered
elliptic source. All five roots are adjoined over Q(c)(a), not over Q(S). -/
noncomputable section
namespace FourCorner.OriginalCoverCompletion.OrderedSource
open FourCorner.Multiquadratic IntermediateField

section GenericFour
variable {F : Type*} [Field F]
def fieldFour (a b c d : F) : IntermediateField F (AlgebraicClosure F) :=
 IntermediateField.adjoin F {radical F a,radical F b,radical F c,radical F d}

theorem four_eq_relative (a b c d : F) : fieldFour a b c d=
    (IntermediateField.adjoin (Multiquadratic.field F a b c) {radical F d}).restrictScalars F := by
  have hh := IntermediateField.adjoin_adjoin_left (F:=F)
    (S:={radical F a,radical F b,radical F c}) ({radical F d}:Set (AlgebraicClosure F))
  have he : ({radical F a,radical F b,radical F c}:Set (AlgebraicClosure F)) ∪ {radical F d}=
      {radical F a,radical F b,radical F c,radical F d} := by ext; simp; tauto
  rw [he] at hh
  exact hh.symm

theorem nonsquare_in_four (a b c d e : F)
    (hd : ¬IsSquare (algebraMap F (Multiquadratic.field F a b c) d))
    (he : ¬IsSquare (algebraMap F (Multiquadratic.field F a b c) e))
    (hde : ¬IsSquare (algebraMap F (Multiquadratic.field F a b c) (d*e)))
    (h2 : (2:F)≠0) : ¬IsSquare (algebraMap F (fieldFour a b c d) e) := by
  let K := Multiquadratic.field F a b c
  let T := IntermediateField.adjoin K {radical F d}
  have hT : T.restrictScalars F=fieldFour a b c d := (four_eq_relative a b c d).symm
  intro hs
  have hsT : IsSquare (algebraMap K T (algebraMap F K e)) := by
    obtain ⟨x,hx⟩ := hs
    let y : T := ⟨x.val,by change x.val∈T.restrictScalars F; rw [hT]; exact x.property⟩
    refine ⟨y,?_⟩
    apply Subtype.ext
    have hh := congrArg (fun z : fieldFour a b c d => (z:AlgebraicClosure F)) hx
    simpa [y] using hh
  have hr : radical F d^2=algebraMap K (AlgebraicClosure F) (algebraMap F K d) :=
    radical_sq F d
  have h2K : (2:K)≠0 := by simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap F K)).mpr h2
  rcases QuadraticSquareCriterion.square_criterion (algebraMap F K d) (algebraMap F K e)
    (radical F d) hr hd h2K hsT with h|h
  · exact he h
  · exact hde (by simpa only [map_mul] using h)
end GenericFour

abbrev root (n : ℚ) (i : Fin 5) := radical BaseField (sourceValue n i)
def firstThree (n : ℚ) := Multiquadratic.field BaseField (sourceValue n 0) (sourceValue n 1) (sourceValue n 2)
def firstFour (n : ℚ) := fieldFour (sourceValue n 0) (sourceValue n 1) (sourceValue n 2) (sourceValue n 3)

/-- Q(X_n), independently presented as the five literal root adjunctions to Q(c)(a). -/
def sourceField (n : ℚ) : IntermediateField BaseField (AlgebraicClosure BaseField) :=
 IntermediateField.adjoin BaseField {root n 0,root n 1,root n 2,root n 3,root n 4}

theorem first_three_independent (n : ℚ) (hn : n≠0) : IndependentSquareclasses BaseField
    (sourceValue n 0) (sourceValue n 1) (sourceValue n 2) := by
  constructor
  · simpa using source_products_nonsquare n hn {0} (by simp)
  · simpa using source_products_nonsquare n hn {1} (by simp)
  · simpa using source_products_nonsquare n hn {2} (by simp)
  · simpa using source_products_nonsquare n hn {0,1} (by simp)
  · simpa using source_products_nonsquare n hn {0,2} (by simp)
  · simpa using source_products_nonsquare n hn {1,2} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {0,1,2} (by simp)

theorem fourth_nonsquare (n : ℚ) (hn : n≠0) :
    ¬IsSquare (algebraMap BaseField (firstThree n) (sourceValue n 3)) := by
  apply nonsquare_in_three _ _ _ _ (first_three_independent n hn)
  · simpa using source_products_nonsquare n hn {3} (by simp)
  · simpa using source_products_nonsquare n hn {0,3} (by simp)
  · simpa using source_products_nonsquare n hn {1,3} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {0,1,3} (by simp)
  · simpa using source_products_nonsquare n hn {2,3} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {0,2,3} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {1,2,3} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {0,1,2,3} (by simp)

theorem fifth_in_three_nonsquare (n : ℚ) (hn : n≠0) :
    ¬IsSquare (algebraMap BaseField (firstThree n) (sourceValue n 4)) := by
  apply nonsquare_in_three _ _ _ _ (first_three_independent n hn)
  · simpa using source_products_nonsquare n hn {4} (by simp)
  · simpa using source_products_nonsquare n hn {0,4} (by simp)
  · simpa using source_products_nonsquare n hn {1,4} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {0,1,4} (by simp)
  · simpa using source_products_nonsquare n hn {2,4} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {0,2,4} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {1,2,4} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {0,1,2,4} (by simp)

theorem fourth_fifth_in_three_nonsquare (n : ℚ) (hn : n≠0) :
    ¬IsSquare (algebraMap BaseField (firstThree n) (sourceValue n 3*sourceValue n 4)) := by
  apply nonsquare_in_three _ _ _ _ (first_three_independent n hn)
  · simpa using source_products_nonsquare n hn {3,4} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {0,3,4} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {1,3,4} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {0,1,3,4} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {2,3,4} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {0,2,3,4} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {1,2,3,4} (by simp)
  · simpa [mul_assoc] using source_products_nonsquare n hn {0,1,2,3,4} (by simp)

theorem fifth_nonsquare (n : ℚ) (hn : n≠0) :
    ¬IsSquare (algebraMap BaseField (firstFour n) (sourceValue n 4)) :=
  nonsquare_in_four _ _ _ _ _ (fourth_nonsquare n hn) (fifth_in_three_nonsquare n hn)
    (fourth_fifth_in_three_nonsquare n hn) (by norm_num)

theorem first_four_finrank (n : ℚ) (hn : n≠0) : Module.finrank BaseField (firstFour n)=16 := by
  have h3 : Module.finrank BaseField (firstThree n)=8 :=
    Multiquadratic.finrank_field_eq_eight BaseField _ _ _ (by norm_num) (first_three_independent n hn)
  have h4 : Module.finrank (firstThree n)
      (IntermediateField.adjoin (firstThree n) {root n 3})=2 := by
    apply Multiquadratic.finrank_adjoin_square_root _ (a:=algebraMap BaseField (firstThree n) (sourceValue n 3))
      (radical_sq BaseField (sourceValue n 3))
    intro u hu
    exact fourth_nonsquare n hn ⟨u,by simpa only [sq] using hu.symm⟩
  have hh := Multiquadratic.finrank_adjoin_union BaseField
    ({root n 0,root n 1,root n 2}:Set (AlgebraicClosure BaseField)) {root n 3}
  have hs : ({root n 0,root n 1,root n 2}:Set (AlgebraicClosure BaseField))∪{root n 3}=
      {root n 0,root n 1,root n 2,root n 3} := by ext; simp; tauto
  rw [hs] at hh
  change Module.finrank BaseField (firstFour n)=Module.finrank BaseField (firstThree n)*
    Module.finrank (firstThree n) (IntermediateField.adjoin (firstThree n) {root n 3}) at hh
  rw [h3,h4] at hh
  exact hh

theorem source_finrank (n : ℚ) (hn : n≠0) : Module.finrank BaseField (sourceField n)=32 := by
  have h5 : Module.finrank (firstFour n)
      (IntermediateField.adjoin (firstFour n) {root n 4})=2 := by
    apply Multiquadratic.finrank_adjoin_square_root _ (a:=algebraMap BaseField (firstFour n) (sourceValue n 4))
      (radical_sq BaseField (sourceValue n 4))
    intro u hu
    exact fifth_nonsquare n hn ⟨u,by simpa only [sq] using hu.symm⟩
  have hh := Multiquadratic.finrank_adjoin_union BaseField
    ({root n 0,root n 1,root n 2,root n 3}:Set (AlgebraicClosure BaseField)) {root n 4}
  have hs : ({root n 0,root n 1,root n 2,root n 3}:Set (AlgebraicClosure BaseField))∪{root n 4}=
      {root n 0,root n 1,root n 2,root n 3,root n 4} := by ext; simp; tauto
  rw [hs] at hh
  change Module.finrank BaseField (sourceField n)=Module.finrank BaseField (firstFour n)*
    Module.finrank (firstFour n) (IntermediateField.adjoin (firstFour n) {root n 4}) at hh
  rw [first_four_finrank n hn,h5] at hh
  exact hh

/-- Every actual chosen ordered root lies in the source field. -/
def orderedRoot (n : ℚ) (i : Fin 5) : sourceField n :=
 ⟨root n i,by
   apply IntermediateField.subset_adjoin
   fin_cases i <;> simp⟩
@[simp] theorem orderedRoot_square (n : ℚ) (i : Fin 5) :
    orderedRoot n i^2=algebraMap BaseField (sourceField n) (sourceValue n i) := by
  apply Subtype.ext
  exact radical_sq _ _

#print axioms source_finrank
#print axioms fifth_nonsquare
#print axioms orderedRoot_square
end FourCorner.OriginalCoverCompletion.OrderedSource
