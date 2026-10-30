import OriginalRadicandIndependence
import geometry.MultiquadraticCoordinateAlgebra

/-! Genuine fourth root irreducibility for the original four-radical generic field. -/
noncomputable section
namespace FourCorner.OriginalCoverCompletion
open FourCorner.Multiquadratic IntermediateField Polynomial

section Generic
variable {F : Type*} [Field F] [CharZero F]

/-- Eight explicit squareclass obstructions suffice at the third quadratic stage.
All field constructions are actual intermediate fields in the algebraic closure. -/
theorem nonsquare_in_three (a b c d : F)
    (hind : IndependentSquareclasses F a b c)
    (h0 : ¬ IsSquare d) (h1 : ¬ IsSquare (a*d))
    (h2 : ¬ IsSquare (b*d)) (h3 : ¬ IsSquare (a*(b*d)))
    (h4 : ¬ IsSquare (c*d)) (h5 : ¬ IsSquare (a*(c*d)))
    (h6 : ¬ IsSquare (b*(c*d))) (h7 : ¬ IsSquare (a*(b*(c*d)))) :
    ¬ IsSquare (algebraMap F (Multiquadratic.field F a b c) d) := by
  let K := IntermediateField.adjoin F {radical F a, radical F b}
  let T := IntermediateField.adjoin K {radical F c}
  have hT : T.restrictScalars F = Multiquadratic.field F a b c :=
    (Tower.third_eq_relative_adjoin F a b c).symm
  have hcK : ¬ IsSquare (algebraMap F K c) := by
    intro hs
    rcases QuadraticSquareCriterion.biquadratic_square_criterion a b c
      (radical F a) (radical F b) (radical_sq F a) (radical_sq F b)
      hind.first hind.second hind.first_second (by norm_num) hs with h|h|h|h
    · exact hind.third h
    · exact hind.first_third h
    · exact hind.second_third h
    · exact hind.all_three (by simpa [mul_assoc] using h)
  intro hs
  have hdT : IsSquare (algebraMap K T (algebraMap F K d)) := by
    obtain ⟨x,hx⟩ := hs
    let y : T := ⟨x.val, by
      change x.val ∈ T.restrictScalars F
      rw [hT]
      exact x.property⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    have hh := congrArg (fun z : Multiquadratic.field F a b c => (z : AlgebraicClosure F)) hx
    simpa [y] using hh
  have hcL : radical F c ^ 2 = algebraMap K (AlgebraicClosure F) (algebraMap F K c) :=
    (radical_sq F c).trans (IsScalarTower.algebraMap_apply F K (AlgebraicClosure F) c)
  rcases QuadraticSquareCriterion.square_criterion (algebraMap F K c) (algebraMap F K d)
    (radical F c) hcL hcK (by norm_num) hdT with hs|hs
  · rcases QuadraticSquareCriterion.biquadratic_square_criterion a b d
      (radical F a) (radical F b) (radical_sq F a) (radical_sq F b)
      hind.first hind.second hind.first_second (by norm_num) hs with h|h|h|h
    · exact h0 h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  · have hs' : IsSquare (algebraMap F K (c*d)) := by simpa only [map_mul] using hs
    rcases QuadraticSquareCriterion.biquadratic_square_criterion a b (c*d)
      (radical F a) (radical F b) (radical_sq F a) (radical_sq F b)
      hind.first hind.second hind.first_second (by norm_num) hs' with h|h|h|h
    · exact h4 h
    · exact h5 h
    · exact h6 h
    · exact h7 h
end Generic

namespace OriginalRadicands
variable (k : Type*) [Field k] [CharZero k]
abbrev BaseField := RatFunc (RatFunc k)

theorem first_three_independent : IndependentSquareclasses (BaseField k)
    (originalValue (K:=k) 0) (originalValue (K:=k) 1) (originalValue (K:=k) 2) := by
  constructor
  · simpa using original_products_nonsquare (K:=k) {0} (by simp)
  · simpa using original_products_nonsquare (K:=k) {1} (by simp)
  · simpa using original_products_nonsquare (K:=k) {2} (by simp)
  · simpa using original_products_nonsquare (K:=k) {0,1} (by simp)
  · simpa using original_products_nonsquare (K:=k) {0,2} (by simp)
  · simpa using original_products_nonsquare (K:=k) {1,2} (by simp)
  · simpa only [Finset.prod_insert,Finset.prod_singleton,Finset.mem_insert,
      Finset.mem_singleton,Fin.reduceEq,or_self,not_false_eq_true,mul_assoc] using
      original_products_nonsquare (K:=k) {0,1,2} (by simp)

abbrev FirstThreeField := Multiquadratic.field (BaseField k)
    (originalValue (K:=k) 0) (originalValue (K:=k) 1) (originalValue (K:=k) 2)

/-- The literal fourth original radicand is irreducible after adjoining the first three. -/
theorem fourth_nonsquare : ¬ IsSquare
    (algebraMap (BaseField k) (FirstThreeField k) (originalValue (K:=k) 3)) := by
  apply nonsquare_in_three _ _ _ _ (first_three_independent k)
  · simpa using original_products_nonsquare (K:=k) {3} (by simp)
  · simpa using original_products_nonsquare (K:=k) {0,3} (by simp)
  · simpa using original_products_nonsquare (K:=k) {1,3} (by simp)
  · simpa [mul_assoc] using original_products_nonsquare (K:=k) {0,1,3} (by simp)
  · simpa using original_products_nonsquare (K:=k) {2,3} (by simp)
  · simpa [mul_assoc] using original_products_nonsquare (K:=k) {0,2,3} (by simp)
  · simpa [mul_assoc] using original_products_nonsquare (K:=k) {1,2,3} (by simp)
  · simpa [mul_assoc] using original_products_nonsquare (K:=k) {0,1,2,3} (by simp)

/-- The independently built generic fourth root field. -/
def GenericField : IntermediateField (BaseField k) (AlgebraicClosure (BaseField k)) :=
  IntermediateField.adjoin (BaseField k)
    {radical (BaseField k) (originalValue (K:=k) 0),
     radical (BaseField k) (originalValue (K:=k) 1),
     radical (BaseField k) (originalValue (K:=k) 2),
     radical (BaseField k) (originalValue (K:=k) 3)}

#print axioms fourth_nonsquare
#print axioms first_three_independent
end OriginalRadicands
end FourCorner.OriginalCoverCompletion
