import OriginalIntegralDomain
import OriginalDeckObstruction

/-! The exact quadratic degree over the genuine original-surface function field.
This module does not identify the independent ordered elliptic source X_n with this field. -/
noncomputable section
namespace FourCorner.OriginalCoverCompletion
open Polynomial FourCorner.Multiquadratic

 theorem constant_nonsquare_ratFunc {k : Type*} [Field k] (c : k) (hc : ¬IsSquare c) :
    ¬ IsSquare (algebraMap k (RatFunc k) c) := by
  intro hs
  have hp : IsSquare (C c : k[X]) :=
    (FourCorner.CoverFields.isSquare_algebraMap_iff (F:=RatFunc k) (C c)).mp (by simpa using hs)
  obtain ⟨p,hp⟩ := hp
  apply hc
  refine ⟨p.eval 0, ?_⟩
  simpa using congrArg (Polynomial.evalRingHom (0:k)) hp

 theorem rational_base_minus_one_nonsquare : ¬ IsSquare (-1 : OriginalTower.F) := by
  have hh := constant_nonsquare_ratFunc (-1 : ℚ) (by
    intro hs; have hh := hs.nonneg; norm_num at hh)
  have hhReal : ¬IsSquare (-1 : RatFunc ℚ) := by simpa using hh
  simpa using constant_nonsquare_ratFunc (-1 : RatFunc ℚ) hhReal


namespace OriginalTower

 theorem firstThree_minus_one_nonsquare : ¬IsSquare (-1 : FirstThreeField) := by
  have hh : ¬IsSquare (algebraMap F FirstThreeField (-1)) := by
    apply nonsquare_in_three _ _ _ _ first_three_independent
    · exact rational_base_minus_one_nonsquare
    all_goals simp only [baseMap_radicand]
    · simpa using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {0} (by simp)
    · simpa using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {1} (by simp)
    · simpa [mul_assoc] using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {0,1} (by simp)
    · simpa using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {2} (by simp)
    · simpa [mul_assoc] using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {0,2} (by simp)
    · simpa [mul_assoc] using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {1,2} (by simp)
    · simpa [mul_assoc] using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {0,1,2} (by simp)
  simpa using hh

 theorem firstThree_negative_fourth_nonsquare : ¬IsSquare
    (algebraMap F FirstThreeField (-(algebraMap Coeff F (radicand 3)))) := by
  apply nonsquare_in_three _ _ _ _ first_three_independent
  all_goals simp only [baseMap_radicand]
  · simpa using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {3} (by simp)
  · simpa using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {0,3} (by simp)
  · simpa using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {1,3} (by simp)
  · simpa [mul_assoc] using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {0,1,3} (by simp)
  · simpa using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {2,3} (by simp)
  · simpa [mul_assoc] using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {0,2,3} (by simp)
  · simpa [mul_assoc] using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {1,2,3} (by simp)
  · simpa [mul_assoc] using OriginalRadicands.original_negative_products_nonsquare (K:=ℚ) {0,1,2,3} (by simp)

 theorem target_minus_one_nonsquare : ¬IsSquare (-1 : Target) := by
  intro hs
  have hs' : IsSquare (algebraMap FirstThreeField Target (-1)) := by simpa using hs
  have hr : radical F (algebraMap Coeff F (radicand 3))^2 =
      algebraMap FirstThreeField (AlgebraicClosure F)
        (algebraMap F FirstThreeField (algebraMap Coeff F (radicand 3))) := by
    exact radical_sq F _
  rcases QuadraticSquareCriterion.square_criterion
    (algebraMap F FirstThreeField (algebraMap Coeff F (radicand 3))) (-1)
    (radical F (algebraMap Coeff F (radicand 3))) hr fourth_nonsquare (by norm_num) hs'
    with hh|hh
  · exact firstThree_minus_one_nonsquare (by simpa using hh)
  · exact firstThree_negative_fourth_nonsquare (by simpa using hh)

/-- An injective evaluation of the actual original quotient into the independently
constructed four-root field, retaining x,y and every ordered radius. -/
def originalGenericMap : OriginalRing →+* Target := genericMap.comp toTower.toRingHom
 theorem originalGenericMap_injective : Function.Injective originalGenericMap :=
  genericMap_injective.comp equiv.injective

def fractionEmbedding : FractionRing OriginalRing →+* Target :=
 IsFractionRing.lift originalGenericMap_injective

end OriginalTower

/-- Minus one is not square in the actual fraction field of the literal original surface. -/
 theorem original_minus_one_nonsquare : ¬IsSquare (-1 : OriginalFunctionField) := by
  intro hs
  obtain ⟨v,hv⟩ := hs
  apply OriginalTower.target_minus_one_nonsquare
  refine ⟨OriginalTower.fractionEmbedding v, ?_⟩
  simpa using congrArg OriginalTower.fractionEmbedding hv

/-- The exact manuscript radicand is nonsquare for every nonzero rational n.
The squarefree and positivity restrictions are therefore fully included. -/
 theorem original_radicand_nonsquare (n : ℚ) (hn : n ≠ 0) :
    ¬IsSquare ((tPlus fieldCoordinates^2-1)/algebraMap ℚ OriginalFunctionField n) :=
  original_radicand_nonsquare_of_minus_one n hn original_minus_one_nonsquare

 def quadraticRadicand (n : ℚ) : OriginalFunctionField :=
    (tPlus fieldCoordinates^2-1)/algebraMap ℚ OriginalFunctionField n

/-- Genuine quadratic adjunction over the independently constructed function field of S. -/
 def OriginalQuadraticField (n : ℚ) : IntermediateField OriginalFunctionField
    (AlgebraicClosure OriginalFunctionField) :=
    IntermediateField.adjoin OriginalFunctionField {radical OriginalFunctionField (quadraticRadicand n)}

/-- The chosen root as an element of the actual two-dimensional extension. -/
def quadraticQ (n : ℚ) : OriginalQuadraticField n :=
 ⟨radical OriginalFunctionField (quadraticRadicand n),
   IntermediateField.subset_adjoin _ _ (by simp)⟩

def quadraticCoordinates (n : ℚ) (i : Fin 6) : OriginalQuadraticField n :=
 algebraMap OriginalFunctionField (OriginalQuadraticField n) (fieldCoordinates i)

 theorem quadraticQ_square (n : ℚ) : quadraticQ n^2=
    algebraMap OriginalFunctionField (OriginalQuadraticField n) (quadraticRadicand n) := by
  apply Subtype.ext
  exact radical_sq _ _

/-- The square equation with the actual ordered original radii inside the extension. -/
 theorem quadraticQ_literal_square (n : ℚ) : quadraticQ n^2=
    ((quadraticCoordinates n 2*quadraticCoordinates n 5+
      quadraticCoordinates n 3*quadraticCoordinates n 4)^2-1)/
      algebraMap ℚ (OriginalQuadraticField n) n := by
  rw [quadraticQ_square]
  simp only [quadraticRadicand,tPlus,map_div₀,map_pow,map_sub,map_add,map_mul,map_one,
    quadraticCoordinates,IsScalarTower.algebraMap_apply ℚ OriginalFunctionField (OriginalQuadraticField n)]

/-- Actual vector-space dimension two, with literal t=r0*r3+r1*r2. -/
 theorem original_quadratic_finrank (n : ℚ) (hn : n ≠ 0) :
    Module.finrank OriginalFunctionField (OriginalQuadraticField n)=2 := by
  apply finrank_adjoin_square_root OriginalFunctionField (radical_sq _ _)
  intro v hv
  exact original_radicand_nonsquare n hn ⟨v,by simpa only [sq,quadraticRadicand] using hv.symm⟩

#print axioms original_minus_one_nonsquare
#print axioms original_radicand_nonsquare
#print axioms original_quadratic_finrank
#print axioms quadraticQ_literal_square
end FourCorner.OriginalCoverCompletion
