import ThetaCoverClassPortable.geometry.AdjacentPolynomials
import ThetaCoverClassPortable.geometry.OppositePlaceOrders
import ThetaCoverClassPortable.geometry.BiquadraticRamification
import ThetaCoverClassPortable.geometry.BiquadraticPolynomialField

/-!
Genuine place orders of the adjacent-model rational functions `g_i / D²`.
The denominator contributes even orders at its zeros, while the quartic and
quadratic degrees cancel at infinity. Actual ramification is computed from
these orders and algebraic squareclass independence.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace FourCorner.AdjacentPlaceOrders

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The order of an actual quotient by a square, including its pole contribution. -/
theorem ord_div_sq (v : Place K F) {f d : F} (hf : f ≠ 0) (hd : d ≠ 0) :
    v.ord (f / d ^ 2) = v.ord f - 2 * v.ord d := by
  have hpow : v.ord (d ^ 2) = 2 * v.ord d := by
    simpa only [zpow_ofNat] using v.ord_zpow d (2 : ℤ)
  rw [div_eq_mul_inv, v.ord_mul hf (inv_ne_zero (pow_ne_zero 2 hd)),
    v.ord_inv, hpow, sub_eq_add_neg]

/-- Both numerator and denominator root multiplicities contribute to a finite order. -/
theorem ord_polynomial_div_sq (z : K) {f d : K[X]} (hf : f ≠ 0) (hd : d ≠ 0) :
    (placeOfPoint K z).ord
      (algebraMap K[X] (RatFunc K) f / (algebraMap K[X] (RatFunc K) d)^2) =
      (f.rootMultiplicity z : ℤ) - 2 * (d.rootMultiplicity z : ℤ) := by
  rw [ord_div_sq _ (RatFunc.algebraMap_ne_zero hf) (RatFunc.algebraMap_ne_zero hd),
    OppositePlaceOrders.ord_polynomial z hf, OppositePlaceOrders.ord_polynomial z hd]

/-- Infinity order of a polynomial quotient by a square. -/
theorem ord_polynomial_div_sq_infty [DecidableEq (RatFunc K)] {f d : K[X]}
    (hf : f ≠ 0) (hd : d ≠ 0) :
    (placeInfty K).ord
      (algebraMap K[X] (RatFunc K) f / (algebraMap K[X] (RatFunc K) d)^2) =
      -(f.natDegree : ℤ) + 2 * (d.natDegree : ℤ) := by
  rw [ord_div_sq _ (RatFunc.algebraMap_ne_zero hf) (RatFunc.algebraMap_ne_zero hd),
    OppositePlaceOrders.ord_polynomial_infty hf,
    OppositePlaceOrders.ord_polynomial_infty hd]
  ring

/-- A coprime polynomial pair cannot vanish simultaneously at a finite point. -/
theorem eval_ne_zero_of_coprime {p q : K[X]} (hpq : IsCoprime p q) {z : K}
    (hpz : p.eval z = 0) : q.eval z ≠ 0 := by
  have h := aeval_ne_zero_of_isCoprime hpq z
  simp only [aeval_def, Algebra.algebraMap_self, eval₂_id] at h
  exact h.resolve_left (not_not.mpr hpz)

open AdjacentPolynomials
variable [CharZero K]

/-- The literal adjacent-model radicands, with the conic denominator retained. -/
def actualValue (c : K) (i : Fin 2) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (radicand c i) /
    (algebraMap K[X] (RatFunc K) (D c))^2

/-- The common base function removing both even pole orders. -/
def denominatorInverse (c : K) : RatFunc K :=
  (algebraMap K[X] (RatFunc K) (D c))⁻¹

theorem actualValue_ne_zero {c : K} (h : Admissible c) (i : Fin 2) :
    actualValue c i ≠ 0 :=
  div_ne_zero (RatFunc.algebraMap_ne_zero (radicand_ne_zero h i))
    (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero (D_ne_zero h)))

theorem denominatorInverse_ne_zero {c : K} (h : Admissible c) :
    denominatorInverse c ≠ 0 :=
  inv_ne_zero (RatFunc.algebraMap_ne_zero (D_ne_zero h))

/-- At a numerator root, coprimality removes the denominator contribution. -/
theorem ord_actualValue_at_root {c z : K} (h : Admissible c) (i : Fin 2)
    (hz : (radicand c i).eval z = 0) :
    (placeOfPoint K z).ord (actualValue c i) = 1 := by
  rw [actualValue, ord_polynomial_div_sq z (radicand_ne_zero h i) (D_ne_zero h),
    rootMultiplicity_eq_one h i hz,
    Polynomial.rootMultiplicity_eq_zero (root_not_denominator_root h i hz)]
  norm_num

/-- Away from both numerator and denominator zeros the actual quotient is a unit. -/
theorem ord_actualValue_off_roots {c z : K} (h : Admissible c) (i : Fin 2)
    (hz : (radicand c i).eval z ≠ 0) (hD : (D c).eval z ≠ 0) :
    (placeOfPoint K z).ord (actualValue c i) = 0 := by
  rw [actualValue, ord_polynomial_div_sq z (radicand_ne_zero h i) (D_ne_zero h),
    Polynomial.rootMultiplicity_eq_zero hz, Polynomial.rootMultiplicity_eq_zero hD]
  norm_num

/-- A root of one numerator leaves the other actual radicand a local unit. -/
theorem ord_other_actualValue_at_root {c z : K} (h : Admissible c)
    {i j : Fin 2} (hji : j ≠ i) (hz : (radicand c i).eval z = 0) :
    (placeOfPoint K z).ord (actualValue c j) = 0 := by
  exact ord_actualValue_off_roots h j
    (eval_ne_zero_of_coprime (radicand_isCoprime h hji.symm) hz)
    (root_not_denominator_root h i hz)

/-- At every finite nonroot the quotient order is twice the common inverse-denominator order. -/
theorem ord_actualValue_eq_twice_denominatorInverse {c z : K}
    (h : Admissible c) (i : Fin 2) (hz : (radicand c i).eval z ≠ 0) :
    (placeOfPoint K z).ord (actualValue c i) =
      2 * (placeOfPoint K z).ord (denominatorInverse c) := by
  rw [actualValue, ord_div_sq _ (RatFunc.algebraMap_ne_zero (radicand_ne_zero h i))
    (RatFunc.algebraMap_ne_zero (D_ne_zero h)),
    OppositePlaceOrders.ord_polynomial_eq_zero_of_eval_ne_zero z hz,
    denominatorInverse, Place.ord_inv]
  ring

/-- Denominator zeros are simple and give a common pole of order two in both radicands. -/
theorem ord_actualValue_at_denominator_root {c z : K} (h : Admissible c)
    (hz : (D c).eval z = 0) (i : Fin 2) :
    (placeOfPoint K z).ord (actualValue c i) = -2 := by
  have hnum := eval_ne_zero_of_coprime (radicand_coprime_D h i).symm hz
  have hmult : (D c).rootMultiplicity z = 1 := by
    apply Nat.le_antisymm (rootMultiplicity_le_one_of_separable (D_separable h) z)
    exact (rootMultiplicity_pos (D_ne_zero h)).2 hz
  rw [actualValue, ord_polynomial_div_sq z (radicand_ne_zero h i) (D_ne_zero h),
    Polynomial.rootMultiplicity_eq_zero hnum, hmult]
  norm_num

/-- Complete finite order formula, retaining the even poles of the literal quotient. -/
theorem ord_actualValue_finite [DecidableEq K] {c : K} (h : Admissible c)
    (i : Fin 2) (z : K) :
    (placeOfPoint K z).ord (actualValue c i) =
      if (radicand c i).eval z = 0 then 1 else if (D c).eval z = 0 then -2 else 0 := by
  split_ifs with hn hd
  · exact ord_actualValue_at_root h i hn
  · exact ord_actualValue_at_denominator_root h hd i
  · exact ord_actualValue_off_roots h i hn hd

/-- Quartic numerator degree and squared quadratic denominator degree cancel at infinity. -/
theorem ord_actualValue_infty [DecidableEq (RatFunc K)] {c : K} (h : Admissible c)
    (i : Fin 2) : (placeInfty K).ord (actualValue c i) = 0 := by
  rw [actualValue, ord_polynomial_div_sq_infty (radicand_ne_zero h i) (D_ne_zero h),
    radicand_natDegree h i, D_natDegree h]
  norm_num

/-- The actual finite places attached to the eight distinct numerator zeros. -/
def finiteRootPlaces (c : K) : Finset (Place K (RatFunc K)) := by
  classical
  exact (allRoots c).image (placeOfPoint K)

theorem mem_allRoots_iff {c : K} (h : Admissible c) (z : K) :
    z ∈ allRoots c ↔ ∃ i : Fin 2, (radicand c i).eval z = 0 := by
  classical
  simp only [allRoots, Finset.mem_union, AdjacentPolynomials.mem_rootSet h]
  constructor
  · rintro (h0 | h1)
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi

theorem mem_finiteRootPlaces {c : K} (h : Admissible c) (z : K) :
    placeOfPoint K z ∈ finiteRootPlaces c ↔ ∃ i : Fin 2, (radicand c i).eval z = 0 := by
  classical
  rw [finiteRootPlaces, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    have hyz := placeOfPoint_injective K heq
    subst y
    exact (mem_allRoots_iff h z).1 hy
  · intro hz
    exact ⟨z, (mem_allRoots_iff h z).2 hz, rfl⟩

theorem finiteRootPlaces_card [IsAlgClosed K] {c : K} (h : Admissible c) :
    (finiteRootPlaces c).card = 8 := by
  classical
  rw [finiteRootPlaces, Finset.card_image_of_injective _ (placeOfPoint_injective K)]
  exact allRoots_card h

theorem placeInfty_not_mem_finiteRootPlaces [DecidableEq (RatFunc K)] (c : K) :
    placeInfty K ∉ finiteRootPlaces c := by
  classical
  rintro hz
  obtain ⟨z, _, heq⟩ := Finset.mem_image.1 hz
  exact placeOfPoint_ne_placeInfty K z heq

/-- The genuine base places with some odd radicand order are exactly the eight finite zeros. -/
theorem exists_odd_ord_iff_mem_finiteRootPlaces [IsAlgClosed K] {c : K}
    (h : Admissible c) (v : Place K (RatFunc K)) :
    (∃ i : Fin 2, Odd (v.ord (actualValue c i))) ↔ v ∈ finiteRootPlaces c := by
  classical
  rcases eq_placeOfPoint_or_eq_placeInfty K v with ⟨z, rfl⟩ | rfl
  · rw [mem_finiteRootPlaces h]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      by_contra hz
      rw [ord_actualValue_eq_twice_denominatorInverse h i hz] at hi
      obtain ⟨n, hn⟩ := hi
      omega
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      rw [ord_actualValue_at_root h i hi]
      exact odd_one
  · simp only [ord_actualValue_infty h, (by norm_num : ¬ Odd (0 : ℤ)), exists_false,
      false_iff]
    exact placeInfty_not_mem_finiteRootPlaces c

/-- All actual base-place order data for the literal adjacent-model radicands. -/
theorem actualRatFuncPlaceOrderData [IsAlgClosed K] [DecidableEq K]
    [DecidableEq (RatFunc K)] {c : K} (h : Admissible c) :
    (finiteRootPlaces c).card = 8 ∧
    (∀ (i : Fin 2) (z : K), (placeOfPoint K z).ord (actualValue c i) =
      if (radicand c i).eval z = 0 then 1 else if (D c).eval z = 0 then -2 else 0) ∧
    (∀ i : Fin 2, (placeInfty K).ord (actualValue c i) = 0) ∧
    (∀ v : Place K (RatFunc K), (∃ i : Fin 2, Odd (v.ord (actualValue c i))) ↔
      v ∈ finiteRootPlaces c) :=
  ⟨finiteRootPlaces_card h, ord_actualValue_finite h, ord_actualValue_infty h,
    exists_odd_ord_iff_mem_finiteRootPlaces h⟩

/-- The actual two-radical extension has index two exactly over the eight simple
numerator zeros. Even denominator poles and infinity are unramified. -/
theorem ramificationIndex_formula_of_independent [IsAlgClosed K]
    [DecidableEq (Place K (RatFunc K))] {c : K} (h : Admissible c)
    (hind : Biquadratic.IndependentSquareclasses (RatFunc K)
      (actualValue c 0) (actualValue c 1))
    (w : Place K (Biquadratic.field (RatFunc K) (actualValue c 0) (actualValue c 1))) :
    w.ramificationIndex (RatFunc K) =
      if w.restrict (RatFunc K) ∈ finiteRootPlaces c then 2 else 1 := by
  classical
  rcases eq_placeOfPoint_or_eq_placeInfty K (w.restrict (RatFunc K)) with ⟨z, hv⟩ | hv
  · have at_root (i : Fin 2) (hz : (radicand c i).eval z = 0) :
        (w.restrict (RatFunc K)).ord (actualValue c i) = 1 := by
      rw [hv]
      exact ord_actualValue_at_root h i hz
    have other_root {i j : Fin 2} (hji : j ≠ i) (hz : (radicand c i).eval z = 0) :
        (w.restrict (RatFunc K)).ord (actualValue c j) = 0 := by
      rw [hv]
      exact ord_other_actualValue_at_root h hji hz
    have in_branch (i : Fin 2) (hz : (radicand c i).eval z = 0) :
        w.restrict (RatFunc K) ∈ finiteRootPlaces c := by
      rw [hv]
      exact (mem_finiteRootPlaces h z).2 ⟨i, hz⟩
    by_cases hz0 : (radicand c 0).eval z = 0
    · rw [if_pos (in_branch 0 hz0)]
      exact Biquadratic.Ramification.ramificationIndex_eq_two_10
        (actualValue c 0) (actualValue c 1) hind w (at_root 0 hz0)
        (other_root (by decide : (1 : Fin 2) ≠ 0) hz0)
    by_cases hz1 : (radicand c 1).eval z = 0
    · rw [if_pos (in_branch 1 hz1)]
      exact Biquadratic.Ramification.ramificationIndex_eq_two_01
        (actualValue c 0) (actualValue c 1) hind w
        (other_root (by decide : (0 : Fin 2) ≠ 1) hz1) (at_root 1 hz1)
    have hnB : w.restrict (RatFunc K) ∉ finiteRootPlaces c := by
      rw [hv, mem_finiteRootPlaces h]
      rintro ⟨i, hi⟩
      fin_cases i
      · exact hz0 hi
      · exact hz1 hi
    rw [if_neg hnB]
    apply Biquadratic.Ramification.ramificationIndex_eq_one_of_common_twice
      (actualValue c 0) (actualValue c 1) hind w (denominatorInverse_ne_zero h)
    · rw [hv]
      exact ord_actualValue_eq_twice_denominatorInverse h 0 hz0
    · rw [hv]
      exact ord_actualValue_eq_twice_denominatorInverse h 1 hz1
  · have hnB : w.restrict (RatFunc K) ∉ finiteRootPlaces c := by
      rw [hv]
      exact placeInfty_not_mem_finiteRootPlaces c
    rw [if_neg hnB]
    apply Biquadratic.Ramification.ramificationIndex_eq_one_of_orders_zero
      (actualValue c 0) (actualValue c 1) hind w
    · rw [hv]
      exact ord_actualValue_infty h 0
    · rw [hv]
      exact ord_actualValue_infty h 1

/-- Squareclass independence of the literal quotients follows from the actual quartic facts. -/
theorem actualValue_independentSquareclasses {c : K} (h : Admissible c) :
    Biquadratic.IndependentSquareclasses (RatFunc K) (actualValue c 0) (actualValue c 1) := by
  exact BiquadraticPolynomialField.independentSquareclasses
    (radicand c 0) (radicand c 1) (D c) (D_ne_zero h)
    (radicand_squarefree h 0) (radicand_squarefree h 1)
    (radicand_not_isUnit h 0) (radicand_not_isUnit h 1)
    (radicand_isCoprime h (by decide : (0 : Fin 2) ≠ 1))

/-- The actual extension's ramification formula, with all algebraic inputs derived
from admissibility of the concrete parameter. -/
theorem ramificationIndex_formula [IsAlgClosed K]
    [DecidableEq (Place K (RatFunc K))] {c : K} (h : Admissible c)
    (w : Place K (Biquadratic.field (RatFunc K) (actualValue c 0) (actualValue c 1))) :
    w.ramificationIndex (RatFunc K) =
      if w.restrict (RatFunc K) ∈ finiteRootPlaces c then 2 else 1 :=
  ramificationIndex_formula_of_independent h (actualValue_independentSquareclasses h) w

/-- Eight genuine branch places together with the actual extension's index formula. -/
theorem actualRamificationData [IsAlgClosed K]
    [DecidableEq (Place K (RatFunc K))] {c : K} (h : Admissible c) :
    (finiteRootPlaces c).card = 8 ∧
    ∀ w : Place K (Biquadratic.field (RatFunc K) (actualValue c 0) (actualValue c 1)),
      w.ramificationIndex (RatFunc K) =
        if w.restrict (RatFunc K) ∈ finiteRootPlaces c then 2 else 1 :=
  ⟨finiteRootPlaces_card h, ramificationIndex_formula h⟩

end FourCorner.AdjacentPlaceOrders

#print axioms FourCorner.AdjacentPlaceOrders.ord_div_sq
#print axioms FourCorner.AdjacentPlaceOrders.ord_polynomial_div_sq
#print axioms FourCorner.AdjacentPlaceOrders.ord_polynomial_div_sq_infty

#print axioms FourCorner.AdjacentPlaceOrders.actualValue_ne_zero

#print axioms FourCorner.AdjacentPlaceOrders.ord_actualValue_at_root

#print axioms FourCorner.AdjacentPlaceOrders.ord_other_actualValue_at_root

#print axioms FourCorner.AdjacentPlaceOrders.ord_actualValue_eq_twice_denominatorInverse

#print axioms FourCorner.AdjacentPlaceOrders.ord_actualValue_at_denominator_root

#print axioms FourCorner.AdjacentPlaceOrders.ord_actualValue_finite

#print axioms FourCorner.AdjacentPlaceOrders.ord_actualValue_infty

#print axioms FourCorner.AdjacentPlaceOrders.finiteRootPlaces_card

#print axioms FourCorner.AdjacentPlaceOrders.exists_odd_ord_iff_mem_finiteRootPlaces

#print axioms FourCorner.AdjacentPlaceOrders.actualRatFuncPlaceOrderData

#print axioms FourCorner.AdjacentPlaceOrders.ramificationIndex_formula

#print axioms FourCorner.AdjacentPlaceOrders.actualRamificationData

#print axioms FourCorner.AdjacentPlaceOrders.actualValue_independentSquareclasses
