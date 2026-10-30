import CommonLiteralField
import geometry.OppositePlaceOrders
import geometry.QuadraticRescaledUnit
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap

/-! Genuine finite and infinity places and exact branch orders in characteristic
different from two. No characteristic-zero curve theorem is instantiated. -/
noncomputable section
open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField
namespace FourCorner.OddFourPlaces
variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (RatFunc K) := Classical.decEq _
def linear (a : K) : RatFunc K := algebraMap K[X] (RatFunc K) (X-C a)
theorem linear_eq (a : K) : linear a = RatFunc.X-algebraMap K (RatFunc K) a := by
  simp only [linear, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rfl
theorem linear_ne_zero (a : K) : linear a ≠ 0 :=
  RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)

theorem ord_linear_finite (z a : K) :
    (placeOfPoint K z).ord (linear a) = if z=a then 1 else 0 := by
  classical
  split_ifs with h
  · subst a; exact OppositePlaceOrders.ord_X_sub_C z
  · apply OppositePlaceOrders.ord_polynomial_eq_zero_of_eval_ne_zero
    simpa using sub_ne_zero.mpr h

theorem ord_linear_infty (a : K) : (placeInfty K).ord (linear a) = -1 := by
  classical
  rw [linear, OppositePlaceOrders.ord_polynomial_infty (X_sub_C_ne_zero a)]
  simp

def branch (t : K) : Fin 4 → K
  | 0 => -(t+1)
  | 1 => t-1
  | 2 => t+1
  | 3 => -(t-1)

theorem radicand_factor (t : K) :
    CommonLiteralField.radicand K t 0 = linear (branch t 0) ∧
    CommonLiteralField.radicand K t 1 = linear (branch t 1) ∧
    CommonLiteralField.radicand K t 2 =
      algebraMap K (RatFunc K) (-(t-1)) * linear (branch t 2) / linear 0 ∧
    CommonLiteralField.radicand K t 3 =
      algebraMap K (RatFunc K) (t+1) * linear (branch t 3) / linear 0 := by
  simp only [CommonLiteralField.radicand, branch, linear_eq, map_neg, map_sub,
    map_add, map_one, map_zero, sub_zero]
  constructor
  · ring
  constructor
  · trivial
  constructor <;> ring

theorem ord_scaled_linear_div (v : Place K (RatFunc K)) (a c : K) (hc : c ≠ 0) :
    v.ord (algebraMap K (RatFunc K) c * linear a / linear 0) =
      v.ord (linear a) - v.ord (linear 0) := by
  have hc' : algebraMap K (RatFunc K) c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  rw [QuadraticRescaledUnit.ord_div v (mul_ne_zero hc' (linear_ne_zero a))
    (linear_ne_zero 0), v.ord_mul hc' (linear_ne_zero a), v.ord_algebraMap]
  ring

theorem ord_finite (t z : K) (htm : t ≠ 1) (htp : t ≠ -1) (i : Fin 4) :
    (placeOfPoint K z).ord (CommonLiteralField.radicand K t i) =
      (if z=branch t i then 1 else 0) - (if 2 ≤ i.val ∧ z=0 then 1 else 0) := by
  classical
  obtain ⟨h0,h1,h2,h3⟩ := radicand_factor t
  have hm : -(t-1) ≠ 0 := neg_ne_zero.mpr (sub_ne_zero.mpr htm)
  have hp : t+1 ≠ 0 := by intro h; apply htp; linear_combination h
  fin_cases i <;> simp only [Fin.reduceFinMk]
  · rw [h0,ord_linear_finite]; simp
  · rw [h1,ord_linear_finite]; simp
  · rw [h2,ord_scaled_linear_div _ _ _ hm,ord_linear_finite,ord_linear_finite]; simp
  · rw [h3,ord_scaled_linear_div _ _ _ hp,ord_linear_finite,ord_linear_finite]; simp

theorem ord_infty (t : K) (htm : t ≠ 1) (htp : t ≠ -1) (i : Fin 4) :
    (placeInfty K).ord (CommonLiteralField.radicand K t i) =
      if i.val < 2 then -1 else 0 := by
  classical
  obtain ⟨h0,h1,h2,h3⟩ := radicand_factor t
  have hm : -(t-1) ≠ 0 := neg_ne_zero.mpr (sub_ne_zero.mpr htm)
  have hp : t+1 ≠ 0 := by intro h; apply htp; linear_combination h
  fin_cases i <;> simp only [Fin.reduceFinMk]
  · rw [h0,ord_linear_infty]; rfl
  · rw [h1,ord_linear_infty]; rfl
  · rw [h2,ord_scaled_linear_div _ _ _ hm,ord_linear_infty,ord_linear_infty]; rfl
  · rw [h3,ord_scaled_linear_div _ _ _ hp,ord_linear_infty,ord_linear_infty]; rfl
variable [NeZero (2 : K)]
theorem branch_ne_zero (t : K) (htm : t ≠ 1) (htp : t ≠ -1) (i : Fin 4) :
    branch t i ≠ 0 := by
  fin_cases i <;> simp only [Fin.reduceFinMk,branch]
  all_goals intro h
  · apply htp; linear_combination -h
  · apply htm; linear_combination h
  · apply htp; linear_combination h
  · apply htm; linear_combination -h

theorem branch_injective (t : K) (ht0 : t ≠ 0) (htm : t ≠ 1) (htp : t ≠ -1) :
    Function.Injective (branch t) := by
  have htwo : (2:K) ≠ 0 := NeZero.ne _
  intro i j h
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk,branch] at h ⊢
  all_goals first | rfl | skip
  all_goals
    exfalso
    first
    | exact htwo (by first | linear_combination h | linear_combination -h)
    | exact ht0 ((mul_eq_zero.mp (show (2:K)*t=0 by
        first | linear_combination h | linear_combination -h)).resolve_left htwo)
    | exact htm (sub_eq_zero.mp ((mul_eq_zero.mp (show (2:K)*(t-1)=0 by
        first | linear_combination h | linear_combination -h)).resolve_left htwo))
    | have hz : t+1=0 := (mul_eq_zero.mp (show (2:K)*(t+1)=0 by
        first | linear_combination h | linear_combination -h)).resolve_left htwo
      apply htp
      linear_combination hz

theorem ord_at_private (t : K) (ht0 : t ≠ 0) (htm : t ≠ 1) (htp : t ≠ -1)
    (i j : Fin 4) :
    (placeOfPoint K (branch t i)).ord (CommonLiteralField.radicand K t j) =
      if i=j then 1 else 0 := by
  rw [ord_finite t _ htm htp]
  have hn := branch_ne_zero t htm htp i
  simp only [hn, and_false, ite_false, sub_zero]
  simp only [(branch_injective t ht0 htm htp).eq_iff]

theorem ord_at_zero (t : K) (htm : t ≠ 1) (htp : t ≠ -1) (i : Fin 4) :
    (placeOfPoint K 0).ord (CommonLiteralField.radicand K t i) =
      if i.val < 2 then 0 else -1 := by
  rw [ord_finite t 0 htm htp]
  have hn := Ne.symm (branch_ne_zero t htm htp i)
  simp only [hn, ite_false, and_true]
  split_ifs <;> omega

theorem ord_linear_off (v : Place K (RatFunc K)) (a : K)
    (hv : v ≠ placeInfty K) (ha : v ≠ placeOfPoint K a) : v.ord (linear a)=0 := by
  obtain ⟨w,rfl⟩ | h := eq_ofHeightOneSpectrum_or_eq_placeInfty v
  · by_contra hn
    have hm := (Place.ord_ofHeightOneSpectrum_ne_zero_iff
      (K := K) (F := RatFunc K) w (X_sub_C_ne_zero a)).mp hn
    have hid : Ideal.span {X-C a} = w.asIdeal :=
      (PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C a)).eq_of_le
        w.isPrime.ne_top (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm))
    have hw : w = heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a) :=
      IsDedekindDomain.HeightOneSpectrum.ext hid.symm
    apply ha
    rw [hw,placeOfPoint_eq_ofHeightOneSpectrum]
  · exact (hv h).elim

theorem ord_off_support (t : K) (htm : t ≠ 1) (htp : t ≠ -1)
    (v : Place K (RatFunc K)) (hv : v ≠ placeInfty K)
    (hz : v ≠ placeOfPoint K 0) (hb : ∀ i, v ≠ placeOfPoint K (branch t i))
    (i : Fin 4) : v.ord (CommonLiteralField.radicand K t i) = 0 := by
  obtain ⟨h0,h1,h2,h3⟩ := radicand_factor t
  have hm : -(t-1) ≠ 0 := neg_ne_zero.mpr (sub_ne_zero.mpr htm)
  have hp : t+1 ≠ 0 := by intro h; apply htp; linear_combination h
  fin_cases i <;> simp only [Fin.reduceFinMk]
  · rw [h0,ord_linear_off v _ hv (hb 0)]
  · rw [h1,ord_linear_off v _ hv (hb 1)]
  · rw [h2,ord_scaled_linear_div _ _ _ hm,
      ord_linear_off v _ hv (hb 2),ord_linear_off v _ hv hz,sub_self]
  · rw [h3,ord_scaled_linear_div _ _ _ hp,
      ord_linear_off v _ hv (hb 3),ord_linear_off v _ hv hz,sub_self]

def privatePlaces (t : K) : Finset (Place K (RatFunc K)) := by
  classical
  exact Finset.univ.image (fun i : Fin 4 => placeOfPoint K (branch t i))
def support (t : K) : Finset (Place K (RatFunc K)) := by
  classical
  exact insert (placeInfty K) (insert (placeOfPoint K 0) (privatePlaces t))

theorem mem_privatePlaces (t : K) (v : Place K (RatFunc K)) :
    v ∈ privatePlaces t ↔ ∃ i, placeOfPoint K (branch t i)=v := by
  classical
  simp [privatePlaces]

theorem zero_not_private (t : K) (htm : t ≠ 1) (htp : t ≠ -1) :
    placeOfPoint K 0 ∉ privatePlaces t := by
  intro h
  obtain ⟨i,hi⟩ := (mem_privatePlaces t _).mp h
  exact branch_ne_zero t htm htp i (placeOfPoint_injective K hi)

theorem infinity_not_private (t : K) : placeInfty K ∉ privatePlaces t := by
  intro h
  obtain ⟨i,hi⟩ := (mem_privatePlaces t _).mp h
  exact placeOfPoint_ne_placeInfty K _ hi

theorem support_card (t : K) (ht0 : t ≠ 0) (htm : t ≠ 1) (htp : t ≠ -1) :
    (support t).card=6 := by
  classical
  have hinj : Function.Injective (fun i : Fin 4 => placeOfPoint K (branch t i)) :=
    (placeOfPoint_injective K).comp (branch_injective t ht0 htm htp)
  have hcard : (privatePlaces t).card=4 := by
    rw [privatePlaces,Finset.card_image_of_injective _ hinj]
    decide
  have hi : placeInfty K ∉ insert (placeOfPoint K 0) (privatePlaces t) := by
    simp only [Finset.mem_insert,not_or]
    exact ⟨Ne.symm (placeOfPoint_ne_placeInfty K 0),infinity_not_private t⟩
  rw [support,Finset.card_insert_of_notMem hi,
    Finset.card_insert_of_notMem (zero_not_private t htm htp),hcard]

theorem exists_odd_iff_mem_support (t : K)
    (ht0 : t ≠ 0) (htm : t ≠ 1) (htp : t ≠ -1) (v : Place K (RatFunc K)) :
    (∃ i, Odd (v.ord (CommonLiteralField.radicand K t i))) ↔ v ∈ support t := by
  classical
  constructor
  · intro h
    by_contra hn
    have hn' : v ≠ placeInfty K ∧ v ≠ placeOfPoint K 0 ∧ v ∉ privatePlaces t := by
      simpa only [support,Finset.mem_insert,not_or] using hn
    obtain ⟨i,hi⟩ := h
    have hb : ∀ i, v ≠ placeOfPoint K (branch t i) := by
      intro j hj
      apply hn'.2.2
      exact (mem_privatePlaces t v).mpr ⟨j,hj.symm⟩
    rw [ord_off_support t htm htp v hn'.1 hn'.2.1 hb i] at hi
    norm_num at hi
  · intro h
    simp only [support,Finset.mem_insert] at h
    rcases h with rfl | rfl | h
    · refine ⟨0,?_⟩
      rw [ord_infty t htm htp]; norm_num
    · refine ⟨2,?_⟩
      rw [ord_at_zero t htm htp]; norm_num
    · obtain ⟨i,rfl⟩ := (mem_privatePlaces t v).mp h
      refine ⟨i,?_⟩
      rw [ord_at_private t ht0 htm htp i i]
      simp

#print axioms support_card
#print axioms exists_odd_iff_mem_support
#print axioms branch_injective
#print axioms ord_at_private
#print axioms ord_at_zero
#print axioms ord_off_support
#print axioms ord_finite
#print axioms ord_infty
end FourCorner.OddFourPlaces
