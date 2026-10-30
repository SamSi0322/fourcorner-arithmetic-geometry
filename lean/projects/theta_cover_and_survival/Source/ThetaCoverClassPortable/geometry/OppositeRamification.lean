import ThetaCoverClassPortable.geometry.OppositeNormalizedField
import ThetaCoverClassPortable.geometry.OppositeNormalizedOrders
import ThetaCoverClassPortable.geometry.MultiquadraticRamification

noncomputable section
open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField
namespace FourCorner.OppositeRamification
open OppositePolynomials OppositePlaceOrders OppositeNormalizedOrders
open OppositeNormalizedField

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [DecidableEq (Place K (RatFunc K))]

/-- The actual degree-eight extension is ramified precisely above the six
simple finite roots; all other places, including infinity, are unramified. -/
theorem ramificationIndex_formula {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0)
    (w : Place K (OppositeNormalizedField.field mu nu)) :
    w.ramificationIndex (RatFunc K) =
      if w.restrict (RatFunc K) ∈ finiteRootPlaces mu nu then 2 else 1 := by
  classical
  let a := value mu nu 0
  let b := value mu nu 1
  let c := value mu nu 2
  have hi : Multiquadratic.IndependentSquareclasses (RatFunc K) a b c :=
    Multiquadratic.independentSquareclasses_of_products (RatFunc K) (value mu nu)
      (OppositeNormalizedField.nonempty_product_nonsquare hmu hnu hA hB hS)
  rcases eq_placeOfPoint_or_eq_placeInfty K (w.restrict (RatFunc K)) with ⟨z, hv⟩ | hv
  · have at_root (i : Fin 3) (hz : (radicand mu nu i).eval z = 0) :
        (w.restrict (RatFunc K)).ord (value mu nu i) = 1 := by
      rw [hv]
      exact ord_normalizedRadicand_at_root hmu hnu hA i hz
    have off_root (i : Fin 3) (hz : (radicand mu nu i).eval z ≠ 0) :
        (w.restrict (RatFunc K)).ord (value mu nu i) = 0 := by
      rw [hv]
      exact ord_normalizedRadicand_off_root hA i hz
    have other_root {i j : Fin 3} (hji : j ≠ i)
        (hz : (radicand mu nu i).eval z = 0) :
        (w.restrict (RatFunc K)).ord (value mu nu j) = 0 := by
      rw [hv]
      exact ord_other_normalizedRadicand_at_root hA hB hS hji hz
    have in_branch (i : Fin 3) (hz : (radicand mu nu i).eval z = 0) :
        w.restrict (RatFunc K) ∈ finiteRootPlaces mu nu := by
      apply (exists_odd_normalized_ord_iff_mem_finiteRootPlaces hmu hnu hA _).mp
      refine ⟨i, ?_⟩
      change Odd ((w.restrict (RatFunc K)).ord (value mu nu i))
      rw [at_root i hz]
      exact odd_one
    by_cases hz0 : (radicand mu nu 0).eval z = 0
    · rw [if_pos (in_branch 0 hz0)]
      exact Multiquadratic.Ramification.ramificationIndex_eq_two_100 a b c hi w
        (at_root 0 hz0) (other_root (by decide : (1 : Fin 3) ≠ 0) hz0)
        (other_root (by decide : (2 : Fin 3) ≠ 0) hz0)
    by_cases hz1 : (radicand mu nu 1).eval z = 0
    · rw [if_pos (in_branch 1 hz1)]
      exact Multiquadratic.Ramification.ramificationIndex_eq_two_010 a b c hi w
        (other_root (by decide : (0 : Fin 3) ≠ 1) hz1) (at_root 1 hz1)
        (other_root (by decide : (2 : Fin 3) ≠ 1) hz1)
    by_cases hz2 : (radicand mu nu 2).eval z = 0
    · rw [if_pos (in_branch 2 hz2)]
      exact Multiquadratic.Ramification.ramificationIndex_eq_two_001 a b c hi w
        (other_root (by decide : (0 : Fin 3) ≠ 2) hz2)
        (other_root (by decide : (1 : Fin 3) ≠ 2) hz2) (at_root 2 hz2)
    have hnB : w.restrict (RatFunc K) ∉ finiteRootPlaces mu nu := by
      intro h
      obtain ⟨i, hi⟩ := (exists_odd_normalized_ord_iff_mem_finiteRootPlaces hmu hnu hA _).mpr h
      change Odd ((w.restrict (RatFunc K)).ord (value mu nu i)) at hi
      fin_cases i
      · change Odd ((w.restrict (RatFunc K)).ord (value mu nu 0)) at hi
        rw [off_root 0 hz0] at hi
        norm_num at hi
      · change Odd ((w.restrict (RatFunc K)).ord (value mu nu 1)) at hi
        rw [off_root 1 hz1] at hi
        norm_num at hi
      · change Odd ((w.restrict (RatFunc K)).ord (value mu nu 2)) at hi
        rw [off_root 2 hz2] at hi
        norm_num at hi
    rw [if_neg hnB]
    exact Multiquadratic.Ramification.ramificationIndex_eq_one_of_orders_zero a b c hi w
      (off_root 0 hz0) (off_root 1 hz1) (off_root 2 hz2)
  · have hnB : w.restrict (RatFunc K) ∉ finiteRootPlaces mu nu := by
      rw [hv]
      exact placeInfty_not_mem_finiteRootPlaces mu nu
    rw [if_neg hnB]
    have ht : (RatFunc.X : RatFunc K) ≠ 0 := by
      simpa only [RatFunc.algebraMap_X] using
        (RatFunc.algebraMap_ne_zero (X_ne_zero : (X : K[X]) ≠ 0))
    have hX : (w.restrict (RatFunc K)).ord RatFunc.X = -1 := by
      rw [hv]
      simpa only [RatFunc.algebraMap_X, natDegree_X, Nat.cast_one] using
        (ord_polynomial_infty (K := K) (X_ne_zero : (X : K[X]) ≠ 0))
    have hord (i : Fin 3) : (w.restrict (RatFunc K)).ord (value mu nu i) =
        2 * (w.restrict (RatFunc K)).ord RatFunc.X := by
      rw [hv]
      change (placeInfty K).ord (actualRadicand mu nu i /
          algebraMap K (RatFunc K) (A mu nu)) = _
      rw [ord_normalizedRadicand_infty hA]
      rw [hv] at hX
      rw [hX]
      norm_num
    exact Multiquadratic.Ramification.ramificationIndex_eq_one_of_common_twice a b c hi w
      ht (hord 0) (hord 1) (hord 2)

#print axioms ramificationIndex_formula
end FourCorner.OppositeRamification
