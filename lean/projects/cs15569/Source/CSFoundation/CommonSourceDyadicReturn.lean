import FourCorner.CommonRootPadicVal
import Mathlib.Tactic

set_option autoImplicit false

namespace FourCorner

/-- The return function in the ordered elliptic source. -/
def commonSourceReturn {K : Type*} [Field K] (n a c : K) : K :=
  (a + c) / (2 * (c + n))

/-- Abscissa after translation by the nontrivial two-torsion point `(0,0)`. -/
def commonSourceTranslateZero {K : Type*} [Field K] (n u : K) : K := -n^2 / u

/-- Abscissa after translation by the nontrivial two-torsion point `(n,0)`. -/
def commonSourceTranslatePlus {K : Type*} [Field K] (n u : K) : K :=
  n + 2*n^2/(u-n)

/-- Abscissa after translation by the nontrivial two-torsion point `(-n,0)`. -/
def commonSourceTranslateMinus {K : Type*} [Field K] (n u : K) : K :=
  -n + 2*n^2/(u+n)

section Algebra
variable {K : Type*} [Field K] [CharZero K] {n u v : K}

theorem commonSource_return_minus_plus (hn : n ≠ 0) (hv : v ≠ 0)
    (hu : u+n ≠ 0) (hvn : v-n ≠ 0) :
    commonSourceReturn n (commonSourceTranslateMinus n u)
      (commonSourceTranslatePlus n v) = n*(u+v)/(2*v*(u+n)) := by
  unfold commonSourceReturn commonSourceTranslateMinus commonSourceTranslatePlus
  field_simp [hn, hv, hu, hvn]
  ring_nf
  field_simp
  ring

theorem commonSource_return_plus_minus (hn : n ≠ 0)
    (hu : u-n ≠ 0) (hvn : v+n ≠ 0) :
    commonSourceReturn n (commonSourceTranslatePlus n u)
      (commonSourceTranslateMinus n v) = (u+v)/(2*(u-n)) := by
  unfold commonSourceReturn commonSourceTranslateMinus commonSourceTranslatePlus
  field_simp [hn, hu, hvn]
  ring_nf
  field_simp

theorem commonSource_return_zero_zero (hn : n ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hvn : v-n ≠ 0) :
    commonSourceReturn n (commonSourceTranslateZero n u)
      (commonSourceTranslateZero n v) = -n*(u+v)/(2*u*(v-n)) := by
  unfold commonSourceReturn commonSourceTranslateZero
  field_simp [hn, hu, hv, hvn]
  ring_nf
  field_simp
  ring

end Algebra

/-- The dyadic valuation of the rational integer two. -/
theorem commonSource_dyadic_val_two : (2 : ℚ_[2]).valuation = 1 := by
  norm_num [Padic.valuation_ofNat]

/-- A negative-valued dyadic number is nonzero. -/
theorem commonSource_dyadic_ne_zero_of_val_neg {u : ℚ_[2]}
    (hu : u.valuation < 0) : u ≠ 0 := by
  intro h
  simp [h] at hu

/-- Multiplication by a nonzero factor of even valuation cannot remove the odd
valuation obstruction from the average of unequal-depth squareclass inputs. -/
theorem commonSource_dyadic_same_val_of_even_scaled_sum {u v c : ℚ_[2]}
    (hu : u ≠ 0) (hv : v ≠ 0) (hc : c ≠ 0)
    (heu : Even u.valuation) (hev : Even v.valuation) (hec : Even c.valuation)
    (hf : Even (((u+v)/2)*c).valuation) : u.valuation = v.valuation := by
  by_contra hne
  have hs := commonRoot_add_ne_zero_of_val_ne hne
  have hvsum := commonRoot_val_add_of_ne hu hv hne
  rw [Padic.valuation_mul (div_ne_zero hs (by norm_num)) hc,
    commonRoot_val_div hs (by norm_num), commonSource_dyadic_val_two, hvsum] at hf
  obtain ⟨a, ha⟩ := heu
  obtain ⟨b, hb⟩ := hev
  obtain ⟨d, hd⟩ := hec
  obtain ⟨e, he⟩ := hf
  rcases le_total u.valuation v.valuation with huv | hvu
  · rw [min_eq_left huv] at he
    omega
  · rw [min_eq_right hvu] at he
    omega

/-- Adding or subtracting a dyadic unit preserves a negative valuation. -/
theorem commonSource_dyadic_offset_vals {n u : ℚ_[2]} (hn : n ≠ 0)
    (hvn : n.valuation = 0) (hu : u.valuation < 0) :
    (u+n ≠ 0 ∧ (u+n).valuation = u.valuation) ∧
      (u-n ≠ 0 ∧ (u-n).valuation = u.valuation) := by
  have hune := commonSource_dyadic_ne_zero_of_val_neg hu
  have hne : u.valuation ≠ n.valuation := by omega
  refine ⟨⟨commonRoot_add_ne_zero_of_val_ne hne, ?_⟩,
    ⟨commonRoot_sub_ne_zero_of_val_ne hne, ?_⟩⟩
  · rw [commonRoot_val_add_of_ne hune hn hne, hvn, min_eq_left (le_of_lt hu)]
  · rw [commonRoot_val_sub_of_ne hune hn hne, hvn, min_eq_left (le_of_lt hu)]

/-- A general quotient form of the unequal-depth obstruction. -/
theorem commonSource_dyadic_same_val_of_even_return {u v a b : ℚ_[2]}
    (hu : u ≠ 0) (hv : v ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (heu : Even u.valuation) (hev : Even v.valuation)
    (hea : Even a.valuation) (heb : Even b.valuation)
    (hf : Even (a*(u+v)/(2*b)).valuation) : u.valuation = v.valuation := by
  by_contra hne
  have hs := commonRoot_add_ne_zero_of_val_ne hne
  have hvsum := commonRoot_val_add_of_ne hu hv hne
  rw [commonRoot_val_div (mul_ne_zero ha hs) (mul_ne_zero (by norm_num) hb),
    Padic.valuation_mul ha hs, Padic.valuation_mul (by norm_num) hb,
    commonSource_dyadic_val_two, hvsum] at hf
  obtain ⟨ku, hku⟩ := heu
  obtain ⟨kv, hkv⟩ := hev
  obtain ⟨ka, hka⟩ := hea
  obtain ⟨kb, hkb⟩ := heb
  obtain ⟨kf, hkf⟩ := hf
  rcases le_total u.valuation v.valuation with huv | hvu
  · rw [min_eq_left huv] at hkf
    omega
  · rw [min_eq_right hvu] at hkf
    omega

/-- The four exact surviving source returns in the dyadic place. -/
def commonSourceDyadicSurviving (n u v f : ℚ_[2]) : Prop :=
  f = n*(u+v)/(2*v*(u+n)) ∨
  f = (u+v)/(2*(u-n)) ∨
  f = (u+v)/(2*(v+n)) ∨
  f = -n*(u+v)/(2*u*(v-n))

/-- Every surviving torsion order forces equal depths as soon as the actual
return has even dyadic valuation.  No bound on the depths is imposed. -/
theorem commonSource_dyadic_surviving_same_val {n u v f : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0)
    (heu : Even u.valuation) (hev : Even v.valuation)
    (hf : commonSourceDyadicSurviving n u v f) (hfe : Even f.valuation) :
    u.valuation = v.valuation := by
  have hun := commonSource_dyadic_ne_zero_of_val_neg hu
  have hvn' := commonSource_dyadic_ne_zero_of_val_neg hv
  obtain ⟨⟨hup, hvup⟩, ⟨hum, hvum⟩⟩ := commonSource_dyadic_offset_vals hn hvn hu
  obtain ⟨⟨hvp, hvvp⟩, ⟨hvm, hvvm⟩⟩ := commonSource_dyadic_offset_vals hn hvn hv
  rcases hf with hf | hf | hf | hf
  · apply commonSource_dyadic_same_val_of_even_return hun hvn' hn
      (mul_ne_zero hvn' hup) heu hev
    · simp [hvn]
    · rw [Padic.valuation_mul hvn' hup, hvup]
      exact hev.add heu
    · simpa only [hf, mul_assoc] using hfe
  · apply commonSource_dyadic_same_val_of_even_return hun hvn' (one_ne_zero) hum heu hev
    · simp
    · simpa only [hvum] using heu
    · simpa only [hf, one_mul] using hfe
  · apply commonSource_dyadic_same_val_of_even_return hun hvn' (one_ne_zero) hvp heu hev
    · simp
    · simpa only [hvvp] using hev
    · simpa only [hf, one_mul] using hfe
  · apply commonSource_dyadic_same_val_of_even_return hun hvn' (neg_ne_zero.mpr hn)
      (mul_ne_zero hun hvm) heu hev
    · simp [commonRoot_val_neg, hvn]
    · rw [Padic.valuation_mul hun hvm, hvvm]
      exact heu.add hev
    · simpa only [hf, mul_assoc] using hfe

/-- The same depth conclusion stated directly on the actual four translated
coordinate pairs, rather than on an independently supplied return formula. -/
theorem commonSource_dyadic_translated_same_val {n u v a c : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0)
    (heu : Even u.valuation) (hev : Even v.valuation)
    (horder :
      (a = commonSourceTranslateMinus n u ∧ c = commonSourceTranslatePlus n v) ∨
      (a = commonSourceTranslatePlus n u ∧ c = commonSourceTranslateMinus n v) ∨
      (a = u ∧ c = v) ∨
      (a = commonSourceTranslateZero n u ∧ c = commonSourceTranslateZero n v))
    (hf : Even (commonSourceReturn n a c).valuation) : u.valuation = v.valuation := by
  apply commonSource_dyadic_surviving_same_val hn hvn hu hv heu hev _ hf
  have hun := commonSource_dyadic_ne_zero_of_val_neg hu
  have hvn' := commonSource_dyadic_ne_zero_of_val_neg hv
  obtain ⟨⟨hup, _⟩, ⟨hum, _⟩⟩ := commonSource_dyadic_offset_vals hn hvn hu
  obtain ⟨⟨hvp, _⟩, ⟨hvm, _⟩⟩ := commonSource_dyadic_offset_vals hn hvn hv
  rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (commonSource_return_minus_plus hn hvn' hup hvm)
  · exact Or.inr (Or.inl (commonSource_return_plus_minus hn hum hvp))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (commonSource_return_zero_zero hn hun hvn' hvm)))

/-- Translation by `(0,0)` reverses the negative abscissa valuation. -/
theorem commonSource_dyadic_translate_zero_val {n u : ℚ_[2]} (hn : n ≠ 0)
    (hvn : n.valuation = 0) (hu : u ≠ 0) :
    commonSourceTranslateZero n u ≠ 0 ∧
    (commonSourceTranslateZero n u).valuation = -u.valuation := by
  have hn2 : -n^2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hn)
  constructor
  · exact div_ne_zero hn2 hu
  · unfold commonSourceTranslateZero
    rw [commonRoot_val_div hn2 hu, commonRoot_val_neg, Padic.valuation_pow, hvn]
    simp

/-- The torsion order `(T₀,O)` always gives the odd return valuation `-1`. -/
theorem commonSource_dyadic_return_zero_identity_val {n u v : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0) :
    (commonSourceReturn n (commonSourceTranslateZero n u) v).valuation = -1 := by
  have hun := commonSource_dyadic_ne_zero_of_val_neg hu
  have hvn' := commonSource_dyadic_ne_zero_of_val_neg hv
  obtain ⟨htn, htv⟩ := commonSource_dyadic_translate_zero_val hn hvn hun
  obtain ⟨⟨hvp, hvvp⟩, _⟩ := commonSource_dyadic_offset_vals hn hvn hv
  have hne : (commonSourceTranslateZero n u).valuation ≠ v.valuation := by omega
  have hs := commonRoot_add_ne_zero_of_val_ne hne
  have hsv := commonRoot_val_add_of_ne htn hvn' hne
  rw [htv, min_eq_right (by omega : v.valuation ≤ -u.valuation)] at hsv
  unfold commonSourceReturn
  rw [commonRoot_val_div hs (mul_ne_zero (by norm_num) hvp),
    Padic.valuation_mul (by norm_num) hvp, commonSource_dyadic_val_two, hvvp, hsv]
  omega

/-- The torsion order `(O,T₀)` gives the return valuation `v₂(u)-1`. -/
theorem commonSource_dyadic_return_identity_zero_val {n u v : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0) :
    (commonSourceReturn n u (commonSourceTranslateZero n v)).valuation =
      u.valuation - 1 := by
  have hun := commonSource_dyadic_ne_zero_of_val_neg hu
  have hvn' := commonSource_dyadic_ne_zero_of_val_neg hv
  obtain ⟨htn, htv⟩ := commonSource_dyadic_translate_zero_val hn hvn hvn'
  have hne : u.valuation ≠ (commonSourceTranslateZero n v).valuation := by omega
  have hs := commonRoot_add_ne_zero_of_val_ne hne
  have hsv := commonRoot_val_add_of_ne hun htn hne
  rw [htv, min_eq_left (by omega : u.valuation ≤ -v.valuation)] at hsv
  have hneq : (commonSourceTranslateZero n v).valuation ≠ n.valuation := by omega
  have hden := commonRoot_add_ne_zero_of_val_ne hneq
  have hvden := commonRoot_val_add_of_ne htn hn hneq
  rw [htv, hvn, min_eq_right (by omega : (0 : ℤ) ≤ -v.valuation)] at hvden
  unfold commonSourceReturn
  rw [commonRoot_val_div hs (mul_ne_zero (by norm_num) hden),
    Padic.valuation_mul (by norm_num) hden, commonSource_dyadic_val_two, hvden, hsv]
  omega

/-- The two torsion orders involving one identity and one `(0,0)` cannot have
an even return valuation for remainders of even negative valuation. -/
theorem commonSource_dyadic_not_even_zero_orders {n u v a c : ℚ_[2]}
    (hn : n ≠ 0) (hvn : n.valuation = 0)
    (hu : u.valuation < 0) (hv : v.valuation < 0) (heu : Even u.valuation)
    (horder :
      (a = commonSourceTranslateZero n u ∧ c = v) ∨
      (a = u ∧ c = commonSourceTranslateZero n v)) :
    ¬ Even (commonSourceReturn n a c).valuation := by
  rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [commonSource_dyadic_return_zero_identity_val hn hvn hu hv]
    norm_num
  · rw [commonSource_dyadic_return_identity_zero_val hn hvn hu hv]
    obtain ⟨k, hk⟩ := heu
    rintro ⟨j, hj⟩
    omega

end FourCorner

#print axioms FourCorner.commonSource_dyadic_translated_same_val
#print axioms FourCorner.commonSource_dyadic_not_even_zero_orders
