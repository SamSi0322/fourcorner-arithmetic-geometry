import CSFoundation.CommonSourceDyadicExcluded

set_option autoImplicit false

namespace FourCorner

/-- The four torsion-coordinate orders whose labels sum to `T₀`. -/
def commonSourceDyadicOrdersOne (n u v a c : ℚ_[2]) : Prop :=
  (a = commonSourceTranslateZero n u ∧ c = v) ∨
  (a = u ∧ c = commonSourceTranslateZero n v) ∨
  (a = commonSourceTranslateMinus n u ∧ c = commonSourceTranslatePlus n v) ∨
  (a = commonSourceTranslatePlus n u ∧ c = commonSourceTranslateMinus n v)

/-- The four torsion-coordinate orders with equal labels. -/
def commonSourceDyadicOrdersSeven (n u v a c : ℚ_[2]) : Prop :=
  (a = commonSourceTranslatePlus n u ∧ c = commonSourceTranslatePlus n v) ∨
  (a = commonSourceTranslateMinus n u ∧ c = commonSourceTranslateMinus n v) ∨
  (a = u ∧ c = v) ∨
  (a = commonSourceTranslateZero n u ∧ c = commonSourceTranslateZero n v)

/-- In the `n ≡ 1 mod 8` torsion relation, even return valuation removes the
orders `(T₀,O),(O,T₀)` and forces equal remainder valuations. -/
theorem commonSource_dyadic_orders_one_same_val {n u v a c : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0)
    (heu : Even u.valuation) (hev : Even v.valuation)
    (horder : commonSourceDyadicOrdersOne n u v a c)
    (hf : Even (commonSourceReturn n a c).valuation) : u.valuation = v.valuation := by
  rcases horder with h | h | h | h
  · exact False.elim (commonSource_dyadic_not_even_zero_orders hn hvn hu hv heu
      (Or.inl h) hf)
  · exact False.elim (commonSource_dyadic_not_even_zero_orders hn hvn hu hv heu
      (Or.inr h) hf)
  · exact commonSource_dyadic_translated_same_val hn hvn hu hv heu hev (Or.inl h) hf
  · exact commonSource_dyadic_translated_same_val hn hvn hu hv heu hev
      (Or.inr (Or.inl h)) hf

/-- In the `n ≡ 7 mod 8` torsion relation, even return valuation removes the
orders `(T₊,T₊),(T₋,T₋)` and forces equal remainder valuations. -/
theorem commonSource_dyadic_orders_seven_same_val {n u v a c : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0)
    (heu : Even u.valuation) (hev : Even v.valuation)
    (horder : commonSourceDyadicOrdersSeven n u v a c)
    (hf : Even (commonSourceReturn n a c).valuation) : u.valuation = v.valuation := by
  rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h | h
  · exact False.elim (commonSource_dyadic_plus_plus_not_even hn hvn hu hv hf)
  · exact False.elim (commonSource_dyadic_minus_minus_not_even hn hvn hu hv hev hf)
  · exact commonSource_dyadic_translated_same_val hn hvn hu hv heu hev
      (Or.inr (Or.inr (Or.inl h))) hf
  · exact commonSource_dyadic_translated_same_val hn hvn hu hv heu hev
      (Or.inr (Or.inr (Or.inr h))) hf

/-- Every odd rational integer is a unit in the actual dyadic field. -/
theorem commonSource_dyadic_odd_int_unit {n : ℤ} (hn : Odd n) :
    (n : ℚ_[2]) ≠ 0 ∧ (n : ℚ_[2]).valuation = 0 := by
  have hn0 : n ≠ 0 := by
    intro h
    simp [h] at hn
  have hnot : ¬ (2 : ℤ) ∣ n := by
    rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := hn
    omega
  constructor
  · exact_mod_cast hn0
  · rw [Padic.valuation_intCast]
    exact_mod_cast (padicValInt.eq_zero_of_not_dvd
      hnot : padicValInt 2 n = 0)

end FourCorner

#print axioms FourCorner.commonSource_dyadic_orders_one_same_val
#print axioms FourCorner.commonSource_dyadic_orders_seven_same_val
#print axioms FourCorner.commonSource_dyadic_odd_int_unit
