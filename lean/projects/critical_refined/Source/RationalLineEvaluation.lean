import RationalPlaceTower
import geometry.OppositePlaceOrders
import ResidueValuationFacts
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one

noncomputable section
namespace FourCorner.RationalLineEvaluation
open AlgebraicCurve AlgebraicCurve.RationalFunctionField Polynomial ResiduePlaceEvaluation
variable {k : Type*} [Field k]

 theorem rational (z : k) : (placeOfPoint k z).IsRational := by
  rw [Place.isRational_iff_deg_eq_one,deg_placeOfPoint]

 theorem linear_mem (z : k) :
    algebraMap k[X] (RatFunc k) (X-C z)∈(placeOfPoint k z).toValuationSubring := by
  apply ((placeOfPoint k z).mem_iff_ord_nonneg (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero z))).mpr
  rw [OppositePlaceOrders.ord_X_sub_C]
  omega

def xAt (z : k) : (placeOfPoint k z).toValuationSubring :=
  ⟨RatFunc.X,by
    have h := (placeOfPoint k z).toValuationSubring.add_mem _ _ (linear_mem z)
      (algebraMap k (placeOfPoint k z).toValuationSubring z).property
    change algebraMap k[X] (RatFunc k) (X-C z)+algebraMap k (RatFunc k) z ∈
      (placeOfPoint k z).toValuationSubring at h
    simpa only [map_sub,RatFunc.algebraMap_X,RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C,sub_add_cancel] using h⟩

theorem evaluate_xAt (z : k) : evaluate (placeOfPoint k z) (rational z) (xAt z)=z := by
  let t : (placeOfPoint k z).toValuationSubring := ⟨algebraMap k[X] (RatFunc k) (X-C z),linear_mem z⟩
  have ht : evaluate (placeOfPoint k z) (rational z) t=0 := by
    apply (ResidueValuationFacts.evaluate_zero_iff_ord_pos _ _ t
      (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero z))).mpr
    change 0<(placeOfPoint k z).ord (algebraMap k[X] (RatFunc k) (X-C z))
    rw [OppositePlaceOrders.ord_X_sub_C]
    omega
  have he : t=xAt z-algebraMap k (placeOfPoint k z).toValuationSubring z := by
    apply Subtype.ext
    simp [t,xAt,RatFunc.algebraMap_eq_C]
  rw [he,map_sub,evaluate_constant,sub_eq_zero] at ht
  exact ht

def polynomialAt (z : k) (p : k[X]) : (placeOfPoint k z).toValuationSubring :=
  Polynomial.aeval (xAt z) p

@[simp] theorem polynomialAt_coe (z : k) (p : k[X]) :
    (polynomialAt z p : RatFunc k)=algebraMap k[X] (RatFunc k) p := by
  have he : (IsScalarTower.toAlgHom k (placeOfPoint k z).toValuationSubring (RatFunc k)).comp
      (Polynomial.aeval (xAt z))=IsScalarTower.toAlgHom k k[X] (RatFunc k) := by
    apply Polynomial.algHom_ext
    simp [xAt,RatFunc.algebraMap_X]
  exact AlgHom.congr_fun he p

@[simp] theorem evaluate_polynomialAt (z : k) (p : k[X]) :
    evaluate (placeOfPoint k z) (rational z) (polynomialAt z p)=p.eval z := by
  have he : (evaluate (placeOfPoint k z) (rational z)).comp (Polynomial.aeval (xAt z))=
      Polynomial.aeval z := by
    apply Polynomial.algHom_ext
    simpa only [AlgHom.comp_apply,Polynomial.aeval_X] using evaluate_xAt z
  simpa only [polynomialAt,AlgHom.comp_apply,Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] using
    AlgHom.congr_fun he p

theorem polynomialAt_unit (z : k) (p : k[X]) (hp : p.eval z≠0) : IsUnit (polynomialAt z p) := by
  apply (ResidueValuationFacts.evaluate_nonzero_iff_unit (placeOfPoint k z) (rational z) _).mp
  rwa [evaluate_polynomialAt]

#print axioms rational
#print axioms evaluate_polynomialAt
#print axioms polynomialAt_unit
end FourCorner.RationalLineEvaluation
