import FourCorner.CommonRootPadicVal
import FourCorner.CommonRootDyadicUnitPair
import FourCorner.CommonRootDyadicFrame
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace FourCorner

/-- The four literal equations give the product of the two signed pair products. -/
theorem commonRoot_dyadic_product_identity {K : Type*} [CommRing K]
    {N X Y A₀ A₁ A₂ A₃ : K}
    (h₀ : A₀^2 = X^2 + Y^2)
    (h₁ : A₁^2 = (N-X)^2 + Y^2)
    (h₂ : A₂^2 = X^2 + (N-Y)^2)
    (h₃ : A₃^2 = (N-X)^2 + (N-Y)^2) :
    (A₀*A₃+A₁*A₂)*(A₀*A₃-A₁*A₂) = -(N^2)*(N-2*X)*(N-2*Y) := by
  calc
    _ = A₀^2*A₃^2-A₁^2*A₂^2 := by ring
    _ = _ := by rw [h₀,h₁,h₂,h₃]; ring

/-- In the dyadic field, 2 has valuation one. -/
theorem commonRoot_dyadic_val_two : (2 : ℚ_[2]).valuation = 1 := by
  simpa using (Padic.valuation_p (p := 2))

/-- The spectral split, assuming the exact unit sum/difference valuation lemma.
The subsequent public theorem supplies this lemma for actual dyadic units. -/
theorem commonRoot_dyadic_spectral_from_min
    {N U V a b : ℚ_[2]} {h : ℤ}
    (hN : N ≠ 0) (hvN : N.valuation = h) (hh : 2 ≤ h)
    (hU : U ≠ 0) (hvU : U.valuation = 1)
    (hvV : V ≠ 0 → 2 ≤ V.valuation)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hva : a.valuation = 0) (hvb : b.valuation = 0)
    (hs : a+b ≠ 0)
    (hprod : (a+b)*(a-b) = -(N^2)*U*V)
    (hmin : a-b ≠ 0 → min (a+b).valuation (a-b).valuation = 1) :
    2 ≤ ((a+b)/N^2).valuation ∨
      (((a+b)/N^2).valuation < 0 ∧ Odd ((a+b)/N^2).valuation) := by
  have hN2 : N^2 ≠ 0 := pow_ne_zero 2 hN
  have hvaldiv : ((a+b)/N^2).valuation = (a+b).valuation - 2*h := by
    rw [commonRoot_val_div hs hN2, Padic.valuation_pow, hvN]
    norm_num
  have hsmall (hone : (a+b).valuation = 1) :
      ((a+b)/N^2).valuation < 0 ∧ Odd ((a+b)/N^2).valuation := by
    rw [hvaldiv, hone]
    constructor
    · omega
    · use -h
      ring
  by_cases hd : a-b = 0
  · have hab : a = b := sub_eq_zero.mp hd
    have he : a+b = 2*a := by rw [← hab]; ring
    have hv : (a+b).valuation = 1 := by
      rw [he, Padic.valuation_mul (by norm_num) ha, commonRoot_dyadic_val_two, hva]
      norm_num
    exact Or.inr (hsmall hv)
  · have hV : V ≠ 0 := by
      intro hz
      rw [hz,mul_zero] at hprod
      exact (mul_ne_zero hs hd) hprod
    have hNU : -(N^2)*U ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hN2) hU
    have hvprod := congrArg Padic.valuation hprod
    rw [Padic.valuation_mul hs hd,
      Padic.valuation_mul hNU hV,
      Padic.valuation_mul (neg_ne_zero.mpr hN2) hU,
      commonRoot_val_neg, Padic.valuation_pow, hvN, hvU] at hvprod
    norm_num at hvprod
    have hm := hmin hd
    have hv := hvV hV
    have hcases : (a+b).valuation = 1 ∨ (a-b).valuation = 1 := by omega
    rcases hcases with hp | hm
    · exact Or.inr (hsmall hp)
    · left
      rw [hvaldiv]
      omega

/-- For actual dyadic units, the only possible return valuations are at least
two or negative odd; the zero reflected coordinate is included. -/
theorem commonRoot_dyadic_spectral_of_product
    {N U V a b : ℚ_[2]} {h : ℤ}
    (hN : N ≠ 0) (hvN : N.valuation = h) (hh : 2 ≤ h)
    (hU : U ≠ 0) (hvU : U.valuation = 1)
    (hvV : V ≠ 0 → 2 ≤ V.valuation)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hva : a.valuation = 0) (hvb : b.valuation = 0)
    (hs : a+b ≠ 0)
    (hprod : (a+b)*(a-b) = -(N^2)*U*V) :
    2 ≤ ((a+b)/N^2).valuation ∨
      (((a+b)/N^2).valuation < 0 ∧ Odd ((a+b)/N^2).valuation) :=
  commonRoot_dyadic_spectral_from_min hN hvN hh hU hvU hvV ha hb hva hvb hs hprod
    (fun hd => commonRoot_dyadic_unit_pair_min ha hb hva hvb hs hd)

/-- Every normalized actual dyadic frame has the asserted spectral valuation. -/
theorem CommonDyadicFrame.classification {t : ℚ_[2]} (F : CommonDyadicFrame t)
    (ht : t ≠ 0) : 2 ≤ t.valuation ∨ (t.valuation < 0 ∧ Odd t.valuation) := by
  have ha : F.A0*F.A3 ≠ 0 := mul_ne_zero F.A0_ne_zero F.A3_ne_zero
  have hb : F.A1*F.A2 ≠ 0 := mul_ne_zero F.A1_ne_zero F.A2_ne_zero
  have hva : (F.A0*F.A3).valuation = 0 := by
    rw [Padic.valuation_mul F.A0_ne_zero F.A3_ne_zero, F.valA0, F.valA3]
    norm_num
  have hvb : (F.A1*F.A2).valuation = 0 := by
    rw [Padic.valuation_mul F.A1_ne_zero F.A2_ne_zero, F.valA1, F.valA2]
    norm_num
  have hs : F.A0*F.A3+F.A1*F.A2 ≠ 0 := by
    intro hz
    apply ht
    rw [F.t_eq, hz, zero_div]
  have hvV : F.N-2*F.Y ≠ 0 → 2 ≤ (F.N-2*F.Y).valuation := by
    intro hn
    exact F.V_case.resolve_left hn
  have hh : (2 : ℤ) ≤ (F.h : ℤ) := by exact_mod_cast F.h_ge_two
  have hclass := commonRoot_dyadic_spectral_of_product F.N_ne_zero F.valN hh
    F.U_ne_zero F.valU hvV ha hb hva hvb hs F.product_identity
  rwa [← F.t_eq] at hclass

#print axioms commonRoot_dyadic_product_identity
#print axioms commonRoot_dyadic_val_two
#print axioms commonRoot_dyadic_spectral_from_min
#print axioms commonRoot_dyadic_spectral_of_product
#print axioms CommonDyadicFrame.classification
end FourCorner
