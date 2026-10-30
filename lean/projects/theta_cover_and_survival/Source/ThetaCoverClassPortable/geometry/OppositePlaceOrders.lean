import ThetaCoverClassPortable.geometry.OppositePolynomials
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification

/-!
Orders of the actual opposite-case radicands at genuine places of `RatFunc K`.
Finite orders are derived from the accepted discrete-valuation order and
polynomial root multiplicity. Infinity is the accepted infinity place.
No branch or ramification data are assumed.
-/

noncomputable section
set_option linter.unusedSectionVars false
open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace FourCorner.OppositePlaceOrders

variable {K : Type*} [Field K]

/-- A polynomial not vanishing at `z` is a unit at its actual finite place. -/
theorem ord_polynomial_eq_zero_of_eval_ne_zero (z : K) {p : K[X]}
    (hp : p.eval z ≠ 0) :
    (placeOfPoint K z).ord (algebraMap K[X] (RatFunc K) p) = 0 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  by_contra h
  have hm := (Place.ord_ofHeightOneSpectrum_ne_zero_iff
    (K := K) (F := RatFunc K)
    (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C z)) hp0).1 h
  change p ∈ Ideal.span {X - C z} at hm
  exact hp ((dvd_iff_isRoot.mp (Ideal.mem_span_singleton.mp hm)))

/-- The accepted normalized place order sends the local parameter `X-z` to one. -/
theorem ord_X_sub_C (z : K) :
    (placeOfPoint K z).ord (algebraMap K[X] (RatFunc K) (X - C z)) = 1 := by
  exact ord_ofHeightOneSpectrum_of_span
    (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C z))
    (X_sub_C_ne_zero z) rfl

/-- The genuine finite-place order of a nonzero polynomial is its root multiplicity. -/
theorem ord_polynomial (z : K) {p : K[X]} (hp : p ≠ 0) :
    (placeOfPoint K z).ord (algebraMap K[X] (RatFunc K) p) =
      (p.rootMultiplicity z : ℤ) := by
  obtain ⟨r, hr⟩ := pow_rootMultiplicity_dvd p z
  have hX : (X : K[X]) - C z ≠ 0 := X_sub_C_ne_zero z
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hp (by simpa using hr)
  set m : ℕ := p.rootMultiplicity z with hm
  have hndvd : ¬ ((X : K[X]) - C z) ∣ r := by
    intro ⟨s, hs⟩
    have hdvd : (X - C z) ^ (m + 1) ∣ p := by
      refine ⟨s, ?_⟩
      calc p = (X - C z) ^ m * ((X - C z) * s) := by rw [hr, hs]
           _ = (X - C z) ^ (m + 1) * s := by ring
    have := (le_rootMultiplicity_iff hp).mpr hdvd
    omega
  have hreval : r.eval z ≠ 0 := fun hz => hndvd (dvd_iff_isRoot.mpr hz)
  have hordr := ord_polynomial_eq_zero_of_eval_ne_zero z hreval
  calc (placeOfPoint K z).ord (algebraMap K[X] (RatFunc K) p)
      = (placeOfPoint K z).ord
          (algebraMap K[X] (RatFunc K) ((X - C z) ^ p.rootMultiplicity z) *
            algebraMap K[X] (RatFunc K) r) := by rw [← map_mul, ← hr]
    _ = (placeOfPoint K z).ord
          (algebraMap K[X] (RatFunc K) ((X - C z) ^ p.rootMultiplicity z)) +
          (placeOfPoint K z).ord (algebraMap K[X] (RatFunc K) r) :=
      (placeOfPoint K z).ord_mul (RatFunc.algebraMap_ne_zero (pow_ne_zero _ hX))
        (RatFunc.algebraMap_ne_zero hr0)
    _ = (placeOfPoint K z).ord
          ((algebraMap K[X] (RatFunc K) (X - C z)) ^ (p.rootMultiplicity z : ℤ)) := by
      rw [hordr, add_zero, map_pow, zpow_natCast]
    _ = (p.rootMultiplicity z : ℤ) := by
      rw [Place.ord_zpow, ord_X_sub_C, mul_one]

/-- The actual infinity-place order of a nonzero polynomial is minus its degree. -/
theorem ord_polynomial_infty [DecidableEq (RatFunc K)] {p : K[X]} (hp : p ≠ 0) :
    (placeInfty K).ord (algebraMap K[X] (RatFunc K) p) = -(p.natDegree : ℤ) := by
  rw [ord_placeInfty (RatFunc.algebraMap_ne_zero hp), RatFunc.intDegree_polynomial]

open OppositePolynomials
variable [CharZero K]

/-- The manuscript's radicands as elements of the actual rational function field. -/
def actualRadicand (mu nu : K) (i : Fin 3) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (radicand mu nu i)

theorem actualRadicand_ne_zero (mu nu : K) (i : Fin 3) :
    actualRadicand mu nu i ≠ 0 :=
  RatFunc.algebraMap_ne_zero (radicand_monic mu nu i).ne_zero

/-- Every finite simple root has genuine discrete valuation order one. -/
theorem ord_radicand_at_root {mu nu z : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (i : Fin 3) (hz : (radicand mu nu i).eval z = 0) :
    (placeOfPoint K z).ord (actualRadicand mu nu i) = 1 := by
  rw [actualRadicand, ord_polynomial z (radicand_monic mu nu i).ne_zero,
    rootMultiplicity_eq_one hmu hnu hA i hz]
  rfl

/-- At every other finite point the radicand has order zero. -/
theorem ord_radicand_off_root {mu nu z : K} (i : Fin 3)
    (hz : (radicand mu nu i).eval z ≠ 0) :
    (placeOfPoint K z).ord (actualRadicand mu nu i) = 0 :=
  ord_polynomial_eq_zero_of_eval_ne_zero z hz

/-- Complete finite order formula for each of the three actual radicands. -/
theorem ord_radicand_finite [DecidableEq K] {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0) (i : Fin 3) (z : K) :
    (placeOfPoint K z).ord (actualRadicand mu nu i) =
      if (radicand mu nu i).eval z = 0 then 1 else 0 := by
  split_ifs with hz
  · exact ord_radicand_at_root hmu hnu hA i hz
  · exact ord_radicand_off_root i hz

/-- Each degree-two radicand has genuine order minus two at infinity. -/
theorem ord_radicand_infty [DecidableEq (RatFunc K)] (mu nu : K) (i : Fin 3) :
    (placeInfty K).ord (actualRadicand mu nu i) = -2 := by
  rw [actualRadicand, ord_polynomial_infty (radicand_monic mu nu i).ne_zero,
    radicand_natDegree]
  rfl

/-- At a root of one radicand, each other radicand is a genuine local unit. -/
theorem ord_other_radicand_at_root {mu nu z : K}
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0)
    {i j : Fin 3} (hji : j ≠ i) (hz : (radicand mu nu i).eval z = 0) :
    (placeOfPoint K z).ord (actualRadicand mu nu j) = 0 := by
  apply ord_radicand_off_root j
  intro hzj
  exact (Finset.disjoint_left.mp (rootSets_pairwise_disjoint hA hB hS hji))
    ((mem_rootSet mu nu z j).2 hzj) ((mem_rootSet mu nu z i).2 hz)

/-- The finite places attached to the six actual polynomial zeros. -/
def finiteRootPlaces (mu nu : K) : Finset (Place K (RatFunc K)) := by
  classical
  exact (allRoots mu nu).image (placeOfPoint K)

theorem mem_finiteRootPlaces (mu nu : K) (v : Place K (RatFunc K)) :
    v ∈ finiteRootPlaces mu nu ↔ ∃ z ∈ allRoots mu nu, placeOfPoint K z = v := by
  classical
  exact Finset.mem_image

theorem finiteRootPlaces_card [IsAlgClosed K] {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    (finiteRootPlaces mu nu).card = 6 := by
  classical
  rw [finiteRootPlaces, Finset.card_image_of_injective _ (placeOfPoint_injective K)]
  exact allRoots_card hmu hnu hA hB hS

theorem placeInfty_not_mem_finiteRootPlaces [DecidableEq (RatFunc K)] (mu nu : K) :
    placeInfty K ∉ finiteRootPlaces mu nu := by
  rintro h
  obtain ⟨z, _, hz⟩ := (mem_finiteRootPlaces mu nu _).1 h
  exact placeOfPoint_ne_placeInfty K z hz

private theorem mem_allRoots_iff (mu nu z : K) :
    z ∈ allRoots mu nu ↔ ∃ i : Fin 3, (radicand mu nu i).eval z = 0 := by
  classical
  simp only [allRoots, Finset.mem_union, OppositePolynomials.mem_rootSet]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi

/-- Exactly the six named finite places have an odd order among the radicands.
This is a statement about the actual base-field valuations, without an assumed
branch locus of a covering curve. -/
theorem exists_odd_ord_iff_mem_finiteRootPlaces [IsAlgClosed K]
    {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (v : Place K (RatFunc K)) :
    (∃ i : Fin 3, Odd (v.ord (actualRadicand mu nu i))) ↔
      v ∈ finiteRootPlaces mu nu := by
  classical
  rcases eq_placeOfPoint_or_eq_placeInfty K v with ⟨z, rfl⟩ | rfl
  · rw [mem_finiteRootPlaces]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨z, (mem_allRoots_iff mu nu z).2 ⟨i, ?_⟩, rfl⟩
      by_contra hz
      rw [ord_radicand_off_root i hz] at hi
      exact (by norm_num : ¬ Odd (0 : ℤ)) hi
    · rintro ⟨y, hy, heq⟩
      have hyz : y = z := placeOfPoint_injective K heq
      subst y
      obtain ⟨i, hi⟩ := (mem_allRoots_iff mu nu z).1 hy
      refine ⟨i, ?_⟩
      rw [ord_radicand_at_root hmu hnu hA i hi]
      exact odd_one
  · constructor
    · rintro ⟨i, hi⟩
      rw [ord_radicand_infty] at hi
      norm_num at hi
    · exact fun h => (placeInfty_not_mem_finiteRootPlaces mu nu h).elim

/-- Complete actual-place order data for the three opposite-case radicands. -/
theorem actualRatFuncPlaceOrderData [IsAlgClosed K] [DecidableEq K]
    [DecidableEq (RatFunc K)] {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    (finiteRootPlaces mu nu).card = 6 ∧
    (∀ (i : Fin 3) (z : K), (placeOfPoint K z).ord (actualRadicand mu nu i) =
      if (radicand mu nu i).eval z = 0 then 1 else 0) ∧
    (∀ i : Fin 3, (placeInfty K).ord (actualRadicand mu nu i) = -2) ∧
    (∀ v : Place K (RatFunc K), (∃ i : Fin 3, Odd (v.ord (actualRadicand mu nu i))) ↔
      v ∈ finiteRootPlaces mu nu) :=
  ⟨finiteRootPlaces_card hmu hnu hA hB hS, ord_radicand_finite hmu hnu hA,
    ord_radicand_infty mu nu, exists_odd_ord_iff_mem_finiteRootPlaces hmu hnu hA⟩

end FourCorner.OppositePlaceOrders

#print axioms FourCorner.OppositePlaceOrders.ord_polynomial_eq_zero_of_eval_ne_zero
#print axioms FourCorner.OppositePlaceOrders.ord_X_sub_C
#print axioms FourCorner.OppositePlaceOrders.ord_polynomial
#print axioms FourCorner.OppositePlaceOrders.ord_polynomial_infty
#print axioms FourCorner.OppositePlaceOrders.actualRadicand_ne_zero
#print axioms FourCorner.OppositePlaceOrders.ord_radicand_at_root
#print axioms FourCorner.OppositePlaceOrders.ord_radicand_off_root
#print axioms FourCorner.OppositePlaceOrders.ord_radicand_finite
#print axioms FourCorner.OppositePlaceOrders.ord_radicand_infty

#print axioms FourCorner.OppositePlaceOrders.ord_other_radicand_at_root

#print axioms FourCorner.OppositePlaceOrders.finiteRootPlaces_card

#print axioms FourCorner.OppositePlaceOrders.placeInfty_not_mem_finiteRootPlaces

#print axioms FourCorner.OppositePlaceOrders.exists_odd_ord_iff_mem_finiteRootPlaces

#print axioms FourCorner.OppositePlaceOrders.actualRatFuncPlaceOrderData
