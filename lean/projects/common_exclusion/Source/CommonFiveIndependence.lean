import CommonLiteralField
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic

noncomputable section
open Polynomial
open scoped BigOperators
namespace FourCorner.CommonFiveIndependence
variable {K : Type*} [Field K] [CharZero K]

def poly (t κ : K) : Fin 5 → K[X]
  | 0 => X + C (t+1)
  | 1 => X - C (t-1)
  | 2 => C (t-1) * (C (t+1)-X) * X
  | 3 => C (t+1) * (X+C (t-1)) * X
  | 4 => C κ * X

def branch (t : K) : Fin 4 → K
  | 0 => -(t+1)
  | 1 => t-1
  | 2 => t+1
  | 3 => -(t-1)

theorem poly_eval_self (t κ : K) (i : Fin 4) :
    (poly t κ i.castSucc).eval (branch t i) = 0 := by
  fin_cases i <;> simp [poly, branch]

theorem poly_derivative_self {t κ : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm : t ≠ -1) (i : Fin 4) :
    (poly t κ i.castSucc).derivative.eval (branch t i) ≠ 0 := by
  have hs : t-1 ≠ 0 := sub_ne_zero.mpr ht1
  have hT : t+1 ≠ 0 := by intro h; apply htm; linear_combination h
  fin_cases i <;> simp [poly, branch, derivative_mul, derivative_sub, derivative_add]
  all_goals repeat' constructor
  all_goals intro he
  all_goals solve
    | exact ht1 (by linear_combination he)
    | exact ht1 (by linear_combination -he)
    | exact htm (by linear_combination he)
    | exact htm (by linear_combination -he)

theorem poly_eval_other {t κ : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm : t ≠ -1) (hκ : κ ≠ 0) (i : Fin 4) (j : Fin 5)
    (hij : j ≠ i.castSucc) : (poly t κ j).eval (branch t i) ≠ 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.castSucc_mk, Fin.mk.injEq] at hij <;> try contradiction
  all_goals
    simp only [poly, branch, eval_add, eval_mul, eval_sub, eval_C, eval_X,
      mul_ne_zero_iff]
    repeat' constructor
    all_goals intro he
    all_goals solve
      | exact ht0 he
      | exact ht0 (by linear_combination he)
      | exact ht0 (by linear_combination (1/2 : K) * he)
      | exact ht0 (by linear_combination (-1/2 : K) * he)
      | exact ht1 (by linear_combination he)
      | exact ht1 (by linear_combination -he)
      | exact ht1 (by linear_combination (1/2 : K) * he)
      | exact ht1 (by linear_combination (-1/2 : K) * he)
      | exact htm (by linear_combination he)
      | exact htm (by linear_combination -he)
      | exact htm (by linear_combination (1/2 : K) * he)
      | exact htm (by linear_combination (-1/2 : K) * he)
      | exact hκ he
      | norm_num at he
      | have hh : (2 : K) = 0 := by linear_combination he
        norm_num at hh
      | have hh : (-2 : K) = 0 := by linear_combination he
        norm_num at hh

lemma square_derivative_zero {f : K[X]} (hf : IsSquare f) (a : K)
    (ha : f.eval a = 0) : f.derivative.eval a = 0 := by
  obtain ⟨g, rfl⟩ := hf
  have hg : g.eval a = 0 := by simpa using ha
  simp [derivative_mul, hg]

lemma product_derivative_nonzero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → K[X]) (i : ι) (hi : i ∈ s) (a : K)
    (hz : (f i).eval a = 0) (hd : (f i).derivative.eval a ≠ 0)
    (ho : ∀ j ∈ s, j ≠ i → (f j).eval a ≠ 0) :
    (∏ j ∈ s, f j).derivative.eval a ≠ 0 := by
  rw [← Finset.mul_prod_erase s f hi]
  simp only [derivative_mul, eval_add, eval_mul, hz, zero_mul, zero_add, add_zero]
  apply mul_ne_zero hd
  rw [eval_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => ho j (Finset.mem_of_mem_erase hj)
    (Finset.ne_of_mem_erase hj))

theorem polynomial_product_nonsquare {t κ : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm : t ≠ -1) (hκ : κ ≠ 0) (s : Finset (Fin 5)) (hne : s.Nonempty) :
    ¬ IsSquare (∏ i ∈ s, poly t κ i) := by
  intro hsq
  by_cases h : ∃ i : Fin 4, i.castSucc ∈ s
  · obtain ⟨i, hi⟩ := h
    have hz : (∏ j ∈ s, poly t κ j).eval (branch t i) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero hi (poly_eval_self t κ i)
    exact product_derivative_nonzero s (poly t κ) i.castSucc hi (branch t i)
      (poly_eval_self t κ i) (poly_derivative_self ht0 ht1 htm i)
      (fun j _ hj => poly_eval_other ht0 ht1 htm hκ i j hj)
      (square_derivative_zero hsq _ hz)
  · have hs : s = {4} := by
      have h0 : (0 : Fin 5) ∉ s := by simpa using fun hi => h ⟨0, hi⟩
      have h1 : (1 : Fin 5) ∉ s := by simpa using fun hi => h ⟨1, hi⟩
      have h2 : (2 : Fin 5) ∉ s := by simpa using fun hi => h ⟨2, hi⟩
      have h3 : (3 : Fin 5) ∉ s := by simpa using fun hi => h ⟨3, hi⟩
      have h4 : (4 : Fin 5) ∈ s := by
        obtain ⟨j,hj⟩ := hne
        fin_cases j <;> simp_all
      ext i
      fin_cases i <;> simp_all
    rw [hs, Finset.prod_singleton] at hsq
    have hd := square_derivative_zero hsq (0 : K) (by simp [poly])
    exact hκ (by simpa [poly] using hd)

/-- Literal five radicands: the original ordered four, followed by ell/κ. -/
def value (t κ : K) : Fin 5 → RatFunc K
  | 0 => CommonLiteralField.radicand K t 0
  | 1 => CommonLiteralField.radicand K t 1
  | 2 => CommonLiteralField.radicand K t 2
  | 3 => CommonLiteralField.radicand K t 3
  | 4 => RatFunc.X / algebraMap K (RatFunc K) κ

def denominator (κ : K) : Fin 5 → RatFunc K
  | 0 => 1
  | 1 => 1
  | 2 => RatFunc.X
  | 3 => RatFunc.X
  | 4 => algebraMap K (RatFunc K) κ

theorem map_poly (t κ : K) (hκ : κ ≠ 0) (i : Fin 5) :
    algebraMap K[X] (RatFunc K) (poly t κ i) =
      value t κ i * (denominator κ i)^2 := by
  have hx : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hk : algebraMap K (RatFunc K) κ ≠ 0 := (_root_.map_ne_zero _).mpr hκ
  fin_cases i <;> simp only [poly, value, denominator, CommonLiteralField.radicand,
    map_add, map_sub, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
    ← RatFunc.algebraMap_eq_C, one_pow, mul_one]
  all_goals field_simp
  all_goals ring

lemma square_map_polynomial_iff (f : K[X]) :
    IsSquare (algebraMap K[X] (RatFunc K) f) ↔ IsSquare f := by
  constructor
  · rintro ⟨b,hb⟩
    have hi : IsIntegral K[X] b := by
      apply IsIntegral.of_pow (n := 2) (by decide)
      rw [pow_two, ← hb]
      exact isIntegral_algebraMap
    obtain ⟨c,hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    refine ⟨c, IsFractionRing.injective K[X] (RatFunc K) ?_⟩
    simpa only [map_mul,hc] using hb
  · rintro ⟨b,rfl⟩
    exact ⟨algebraMap K[X] (RatFunc K) b, map_mul _ b b⟩

/-- Every nonempty product of the actual five literal radicands is nonsquare.
This works over every characteristic-zero constant field, in particular Qbar. -/
theorem nonempty_product_nonsquare {t κ : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm : t ≠ -1) (hκ : κ ≠ 0) (s : Finset (Fin 5)) (hne : s.Nonempty) :
    ¬ IsSquare (∏ i ∈ s, value t κ i) := by
  intro h
  apply polynomial_product_nonsquare ht0 ht1 htm hκ s hne
  apply (square_map_polynomial_iff _).mp
  have hd : IsSquare ((∏ i ∈ s, denominator κ i)^2) :=
    ⟨∏ i ∈ s, denominator κ i, pow_two _⟩
  have he : algebraMap K[X] (RatFunc K) (∏ i ∈ s, poly t κ i) =
      (∏ i ∈ s, value t κ i) * (∏ i ∈ s, denominator κ i)^2 := by
    simp only [map_prod, map_poly t κ hκ, Finset.prod_mul_distrib, Finset.prod_pow]
  rw [he]
  exact h.mul hd

theorem value_castSucc (t κ : K) (i : Fin 4) :
    value t κ i.castSucc = CommonLiteralField.radicand K t i := by
  fin_cases i <;> rfl

/-- Independence for the actual four-radical common function field. -/
theorem four_product_nonsquare {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm : t ≠ -1) (s : Finset (Fin 4)) (hne : s.Nonempty) :
    ¬ IsSquare (∏ i ∈ s, CommonLiteralField.radicand K t i) := by
  have h := nonempty_product_nonsquare ht0 ht1 htm (one_ne_zero : (1 : K) ≠ 0)
    (s.map Fin.castSuccEmb) (Finset.map_nonempty.mpr hne)
  simpa only [Finset.prod_map, Fin.coe_castSuccEmb, value_castSucc] using h

#print axioms nonempty_product_nonsquare
#print axioms four_product_nonsquare
end FourCorner.CommonFiveIndependence
