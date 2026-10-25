import CSFoundation.CommonSourceDyadicReturn

set_option autoImplicit false

namespace FourCorner

section Algebra
variable {K : Type*} [Field K] [CharZero K] {n u v : K}

/-- Exact return for the order `(T₊,T₊)`. -/
theorem commonSource_return_plus_plus (hn : n ≠ 0) (hv : v ≠ 0)
    (hu : u-n ≠ 0) (hvn : v-n ≠ 0) :
    commonSourceReturn n (commonSourceTranslatePlus n u)
      (commonSourceTranslatePlus n v) = (u*v-n^2)/(2*v*(u-n)) := by
  unfold commonSourceReturn commonSourceTranslatePlus
  field_simp [hn, hv, hu, hvn]
  ring_nf
  field_simp
  ring

/-- Exact return for the order `(T₋,T₋)`. -/
theorem commonSource_return_minus_minus (hn : n ≠ 0)
    (hu : u+n ≠ 0) (hvn : v+n ≠ 0) :
    commonSourceReturn n (commonSourceTranslateMinus n u)
      (commonSourceTranslateMinus n v) = -(u*v-n^2)/(2*n*(u+n)) := by
  unfold commonSourceReturn commonSourceTranslateMinus
  field_simp [hn, hu, hvn]
  ring_nf
  field_simp
  ring

end Algebra

/-- A product of two negative-depth abscissae dominates the square of a dyadic unit. -/
theorem commonSource_dyadic_product_sub_unit_square {n u v : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0) :
    u*v-n^2 ≠ 0 ∧ (u*v-n^2).valuation = u.valuation+v.valuation := by
  have hun := commonSource_dyadic_ne_zero_of_val_neg hu
  have hvn' := commonSource_dyadic_ne_zero_of_val_neg hv
  have hprod : (u*v).valuation = u.valuation+v.valuation := Padic.valuation_mul hun hvn'
  have hsq : (n^2).valuation = 0 := by simp [Padic.valuation_pow, hvn]
  have hne : (u*v).valuation ≠ (n^2).valuation := by rw [hprod, hsq]; omega
  refine ⟨commonRoot_sub_ne_zero_of_val_ne hne, ?_⟩
  rw [commonRoot_val_sub_of_ne (mul_ne_zero hun hvn') (pow_ne_zero _ hn) hne,
    hprod, hsq, min_eq_left (by omega)]

/-- The `(T₊,T₊)` source order always has return valuation `-1`. -/
theorem commonSource_dyadic_plus_plus_val {n u v : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0) :
    (commonSourceReturn n (commonSourceTranslatePlus n u)
      (commonSourceTranslatePlus n v)).valuation = -1 := by
  have hvn' := commonSource_dyadic_ne_zero_of_val_neg hv
  obtain ⟨_, ⟨hum, hvum⟩⟩ := commonSource_dyadic_offset_vals hn hvn hu
  obtain ⟨_, ⟨hvm, _⟩⟩ := commonSource_dyadic_offset_vals hn hvn hv
  obtain ⟨hnum, hvnum⟩ := commonSource_dyadic_product_sub_unit_square hn hvn hu hv
  rw [commonSource_return_plus_plus hn hvn' hum hvm,
    commonRoot_val_div hnum (mul_ne_zero (mul_ne_zero (by norm_num) hvn') hum),
    Padic.valuation_mul (mul_ne_zero (by norm_num) hvn') hum,
    Padic.valuation_mul (by norm_num) hvn', commonSource_dyadic_val_two, hvum, hvnum]
  omega

/-- The `(T₋,T₋)` source order has return valuation `v₂(v)-1`. -/
theorem commonSource_dyadic_minus_minus_val {n u v : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0) :
    (commonSourceReturn n (commonSourceTranslateMinus n u)
      (commonSourceTranslateMinus n v)).valuation = v.valuation-1 := by
  obtain ⟨⟨hup, hvup⟩, _⟩ := commonSource_dyadic_offset_vals hn hvn hu
  obtain ⟨⟨hvp, _⟩, _⟩ := commonSource_dyadic_offset_vals hn hvn hv
  obtain ⟨hnum, hvnum⟩ := commonSource_dyadic_product_sub_unit_square hn hvn hu hv
  rw [commonSource_return_minus_minus hn hup hvp,
    commonRoot_val_div (neg_ne_zero.mpr hnum) (mul_ne_zero (mul_ne_zero (by norm_num) hn) hup),
    commonRoot_val_neg, Padic.valuation_mul (mul_ne_zero (by norm_num) hn) hup,
    Padic.valuation_mul (by norm_num) hn, commonSource_dyadic_val_two, hvn, hvup, hvnum]
  omega

/-- The `(T₊,T₊)` return cannot have even dyadic valuation. -/
theorem commonSource_dyadic_plus_plus_not_even {n u v : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0) :
    ¬ Even (commonSourceReturn n (commonSourceTranslatePlus n u)
      (commonSourceTranslatePlus n v)).valuation := by
  rw [commonSource_dyadic_plus_plus_val hn hvn hu hv]
  norm_num

/-- If `v` has even depth valuation, the `(T₋,T₋)` return cannot have even valuation. -/
theorem commonSource_dyadic_minus_minus_not_even {n u v : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0) (hev : Even v.valuation) :
    ¬ Even (commonSourceReturn n (commonSourceTranslateMinus n u)
      (commonSourceTranslateMinus n v)).valuation := by
  rw [commonSource_dyadic_minus_minus_val hn hvn hu hv]
  obtain ⟨k, hk⟩ := hev
  rintro ⟨l, hl⟩
  omega

end FourCorner

#print axioms FourCorner.commonSource_dyadic_plus_plus_val
#print axioms FourCorner.commonSource_dyadic_minus_minus_val
#print axioms FourCorner.commonSource_dyadic_plus_plus_not_even
#print axioms FourCorner.commonSource_dyadic_minus_minus_not_even
