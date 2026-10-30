import geometry.OppositePlaceOrders
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap

/-!
Genuine place orders for the normalized affine-model radicands `f_i / A`.
The normalization constant is a unit at every place over the constant field,
so these orders agree with the actual unnormalized polynomial orders.
-/

noncomputable section
set_option linter.unusedSectionVars false
open AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace FourCorner.OppositeNormalizedOrders

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Dividing by a nonzero constant leaves every genuine place order unchanged. -/
theorem ord_div_constant (v : Place K F) (f : F) {c : K} (hc : c ≠ 0) :
    v.ord (f / algebraMap K F c) = v.ord f := by
  by_cases hf : f = 0
  · simp [hf, v.ord_zero]
  · have hcF : algebraMap K F c ≠ 0 := (map_ne_zero _).2 hc
    rw [div_eq_mul_inv, v.ord_mul hf (inv_ne_zero hcF), v.ord_inv,
      v.ord_algebraMap, neg_zero, add_zero]

open OppositePolynomials OppositePlaceOrders
variable [CharZero K]

/-- Normalization by `A` changes none of the actual rational-function place orders. -/
theorem ord_normalizedRadicand {mu nu : K} (hA : A mu nu ≠ 0)
    (v : Place K (RatFunc K)) (i : Fin 3) :
    v.ord (actualRadicand mu nu i / algebraMap K (RatFunc K) (A mu nu)) =
      v.ord (actualRadicand mu nu i) :=
  ord_div_constant v _ hA

/-- The normalized affine-model radicands are nonzero elements of the base field. -/
theorem normalizedRadicand_ne_zero {mu nu : K} (hA : A mu nu ≠ 0) (i : Fin 3) :
    actualRadicand mu nu i / algebraMap K (RatFunc K) (A mu nu) ≠ 0 :=
  div_ne_zero (actualRadicand_ne_zero mu nu i) ((map_ne_zero _).2 hA)

theorem ord_normalizedRadicand_at_root {mu nu z : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (i : Fin 3) (hz : (radicand mu nu i).eval z = 0) :
    (placeOfPoint K z).ord
      (actualRadicand mu nu i / algebraMap K (RatFunc K) (A mu nu)) = 1 := by
  rw [ord_normalizedRadicand hA]
  exact ord_radicand_at_root hmu hnu hA i hz

theorem ord_normalizedRadicand_off_root {mu nu z : K}
    (hA : A mu nu ≠ 0) (i : Fin 3) (hz : (radicand mu nu i).eval z ≠ 0) :
    (placeOfPoint K z).ord
      (actualRadicand mu nu i / algebraMap K (RatFunc K) (A mu nu)) = 0 := by
  rw [ord_normalizedRadicand hA]
  exact ord_radicand_off_root i hz

theorem ord_normalizedRadicand_finite [DecidableEq K] {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0) (i : Fin 3) (z : K) :
    (placeOfPoint K z).ord
      (actualRadicand mu nu i / algebraMap K (RatFunc K) (A mu nu)) =
      if (radicand mu nu i).eval z = 0 then 1 else 0 := by
  rw [ord_normalizedRadicand hA]
  exact ord_radicand_finite hmu hnu hA i z

theorem ord_normalizedRadicand_infty [DecidableEq (RatFunc K)] {mu nu : K}
    (hA : A mu nu ≠ 0) (i : Fin 3) :
    (placeInfty K).ord
      (actualRadicand mu nu i / algebraMap K (RatFunc K) (A mu nu)) = -2 := by
  rw [ord_normalizedRadicand hA]
  exact ord_radicand_infty mu nu i

/-- At a root of one normalized radicand the other two are local units. -/
theorem ord_other_normalizedRadicand_at_root {mu nu z : K}
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0)
    {i j : Fin 3} (hji : j ≠ i) (hz : (radicand mu nu i).eval z = 0) :
    (placeOfPoint K z).ord
      (actualRadicand mu nu j / algebraMap K (RatFunc K) (A mu nu)) = 0 := by
  rw [ord_normalizedRadicand hA]
  exact ord_other_radicand_at_root hA hB hS hji hz

/-- Exactly the same six genuine finite places have odd normalized-radicand order. -/
theorem exists_odd_normalized_ord_iff_mem_finiteRootPlaces [IsAlgClosed K]
    {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (v : Place K (RatFunc K)) :
    (∃ i : Fin 3, Odd (v.ord
      (actualRadicand mu nu i / algebraMap K (RatFunc K) (A mu nu)))) ↔
      v ∈ finiteRootPlaces mu nu := by
  simp only [ord_normalizedRadicand hA]
  exact exists_odd_ord_iff_mem_finiteRootPlaces hmu hnu hA v

/-- Complete normalized affine-model order data, proved at actual places. -/
theorem actualNormalizedPlaceOrderData [IsAlgClosed K] [DecidableEq K]
    [DecidableEq (RatFunc K)] {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    (finiteRootPlaces mu nu).card = 6 ∧
    (∀ (i : Fin 3) (z : K), (placeOfPoint K z).ord
      (actualRadicand mu nu i / algebraMap K (RatFunc K) (A mu nu)) =
      if (radicand mu nu i).eval z = 0 then 1 else 0) ∧
    (∀ i : Fin 3, (placeInfty K).ord
      (actualRadicand mu nu i / algebraMap K (RatFunc K) (A mu nu)) = -2) ∧
    (∀ v : Place K (RatFunc K), (∃ i : Fin 3, Odd (v.ord
      (actualRadicand mu nu i / algebraMap K (RatFunc K) (A mu nu)))) ↔
      v ∈ finiteRootPlaces mu nu) :=
  ⟨finiteRootPlaces_card hmu hnu hA hB hS,
    ord_normalizedRadicand_finite hmu hnu hA,
    ord_normalizedRadicand_infty hA,
    exists_odd_normalized_ord_iff_mem_finiteRootPlaces hmu hnu hA⟩

end FourCorner.OppositeNormalizedOrders

#print axioms FourCorner.OppositeNormalizedOrders.ord_div_constant
#print axioms FourCorner.OppositeNormalizedOrders.ord_normalizedRadicand
#print axioms FourCorner.OppositeNormalizedOrders.normalizedRadicand_ne_zero
#print axioms FourCorner.OppositeNormalizedOrders.ord_normalizedRadicand_at_root
#print axioms FourCorner.OppositeNormalizedOrders.ord_normalizedRadicand_off_root
#print axioms FourCorner.OppositeNormalizedOrders.ord_normalizedRadicand_finite
#print axioms FourCorner.OppositeNormalizedOrders.ord_normalizedRadicand_infty
#print axioms FourCorner.OppositeNormalizedOrders.ord_other_normalizedRadicand_at_root
#print axioms FourCorner.OppositeNormalizedOrders.exists_odd_normalized_ord_iff_mem_finiteRootPlaces
#print axioms FourCorner.OppositeNormalizedOrders.actualNormalizedPlaceOrderData
