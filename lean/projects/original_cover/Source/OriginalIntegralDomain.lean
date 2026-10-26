import OriginalTowerPresentation
import FourRadicalGenericField

/-! Integrality of the genuine original coordinate ring, via its four independent roots. -/
noncomputable section
namespace FourCorner.OriginalCoverCompletion.OriginalTower
open Polynomial FourCorner.Multiquadratic
abbrev F := OriginalRadicands.BaseField ℚ

def baseMap : Coeff →+* F :=
 (algebraMap (RatFunc ℚ)[X] F).comp (Polynomial.mapRingHom (algebraMap ℚ[X] (RatFunc ℚ)))

instance : Algebra Coeff F := baseMap.toAlgebra

 theorem baseMap_injective : Function.Injective (algebraMap Coeff F) :=
  (RatFunc.algebraMap_injective (RatFunc ℚ)).comp
    (Polynomial.map_injective _ (RatFunc.algebraMap_injective ℚ))

 theorem baseMap_x : algebraMap Coeff F x=algebraMap (RatFunc ℚ) F RatFunc.X := by
  change baseMap x=_
  simp [baseMap,x,RatFunc.algebraMap_X]
 theorem baseMap_y : algebraMap Coeff F y=(RatFunc.X : F) := by
  change baseMap y=_
  simp [baseMap,y,RatFunc.algebraMap_X]

 theorem baseMap_radicand (i : Fin 4) :
    algebraMap Coeff F (radicand i)=OriginalRadicands.originalValue (K:=ℚ) i := by
  fin_cases i <;> simp [radicand,map_add,map_sub,map_pow,baseMap_x,baseMap_y,
    OriginalRadicands.originalValue,OriginalRadicands.originalPolynomial,OriginalRadicands.f,
    RatFunc.algebraMap_X,RatFunc.algebraMap_C] <;> ring

abbrev FirstThreeField := CoordinateAlgebra.field₃ Coeff F (radicand 0) (radicand 1) (radicand 2)
abbrev Target := IntermediateField.adjoin FirstThreeField
  {radical F (algebraMap Coeff F (radicand 3))}
def fourthRoot : Target := ⟨radical F (algebraMap Coeff F (radicand 3)),
  IntermediateField.subset_adjoin _ _ (by simp)⟩

 theorem first_three_independent : IndependentSquareclasses F
    (algebraMap Coeff F (radicand 0)) (algebraMap Coeff F (radicand 1))
    (algebraMap Coeff F (radicand 2)) := by
  simp only [baseMap_radicand]
  exact OriginalRadicands.first_three_independent ℚ

 theorem fourth_nonsquare : ¬ IsSquare
    (algebraMap F FirstThreeField (algebraMap Coeff F (radicand 3))) := by
  apply nonsquare_in_three _ _ _ _ first_three_independent
  all_goals simp only [baseMap_radicand]
  · simpa using OriginalRadicands.original_products_nonsquare (K:=ℚ) {3} (by simp)
  · simpa using OriginalRadicands.original_products_nonsquare (K:=ℚ) {0,3} (by simp)
  · simpa using OriginalRadicands.original_products_nonsquare (K:=ℚ) {1,3} (by simp)
  · simpa [mul_assoc] using OriginalRadicands.original_products_nonsquare (K:=ℚ) {0,1,3} (by simp)
  · simpa using OriginalRadicands.original_products_nonsquare (K:=ℚ) {2,3} (by simp)
  · simpa [mul_assoc] using OriginalRadicands.original_products_nonsquare (K:=ℚ) {0,2,3} (by simp)
  · simpa [mul_assoc] using OriginalRadicands.original_products_nonsquare (K:=ℚ) {1,2,3} (by simp)
  · simpa [mul_assoc] using OriginalRadicands.original_products_nonsquare (K:=ℚ) {0,1,2,3} (by simp)

 theorem fourthRoot_square : fourthRoot^2=
    algebraMap FirstThreeField Target (algebraMap F FirstThreeField (algebraMap Coeff F (radicand 3))) := by
  apply Subtype.ext
  exact radical_sq F _

abbrev thirdMap := CoordinateAlgebra.map₃ Coeff F (radicand 0) (radicand 1) (radicand 2)

theorem fourth_root_equation : fourthEquation.eval₂
    ((algebraMap FirstThreeField Target).comp thirdMap) fourthRoot=0 := by
  simp only [fourthEquation,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,RingHom.comp_apply,
    CoordinateAlgebra.map₃_algebraMap,fourthRoot_square,sub_self]

def genericMap : Ring →+* Target := AdjoinRoot.lift
  ((algebraMap FirstThreeField Target).comp thirdMap) fourthRoot fourth_root_equation

 theorem genericMap_injective : Function.Injective genericMap := by
  apply AdjoinRootInjective.lift_injective_of_monic_of_irreducible_map
    thirdMap (CoordinateAlgebra.map₃_injective Coeff F _ _ _ baseMap_injective (by norm_num)
      first_three_independent) fourthEquation (monic_X_pow_sub_C _ (by decide))
    (algebraMap FirstThreeField Target) fourthRoot
  · simp only [fourthEquation,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,
      Polynomial.map_C,CoordinateAlgebra.map₃_algebraMap]
    apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
    intro u hu
    exact fourth_nonsquare ⟨u,by simpa only [sq] using hu.symm⟩

instance towerRing_isDomain : IsDomain Ring := Function.Injective.isDomain genericMap genericMap_injective

/-- The original four-equation affine coordinate ring is genuinely integral. -/
instance originalRing_isDomain : IsDomain OriginalRing :=
 Function.Injective.isDomain toTower.toRingHom equiv.injective

#print axioms originalRing_isDomain
#print axioms genericMap_injective
#print axioms baseMap_radicand
end FourCorner.OriginalCoverCompletion.OriginalTower
