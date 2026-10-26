import HasseConicTangentParity

/-! Exact rational scaling to a primitive integral chart at an arbitrary
prime. No height bound, finite parameter subset or valuation depth bound. -/
namespace FourCorner.HasseRationalNormalization

variable {q : ℕ} [Fact q.Prime]

theorem inverse_scale_valuation (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    padicValRat q (x⁻¹*y)=padicValRat q y-padicValRat q x := by
  rw [padicValRat.mul (inv_ne_zero hx) hy,padicValRat.inv]
  ring

/-- One of the three original nonzero rational coordinates supplies a
rational normalization that is integral and primitive in Q_q. -/
theorem exists_primitive_rational_scale (x y z : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    ∃ s : ℚ, s ≠ 0 ∧
      0≤padicValRat q (s*x) ∧ 0≤padicValRat q (s*y) ∧ 0≤padicValRat q (s*z) ∧
      (padicValRat q (s*x)=0 ∨ padicValRat q (s*y)=0 ∨ padicValRat q (s*z)=0) := by
  by_cases hxy : padicValRat q x≤padicValRat q y
  · by_cases hxz : padicValRat q x≤padicValRat q z
    · refine ⟨x⁻¹,inv_ne_zero hx,?_,?_,?_,?_⟩
      · rw [inverse_scale_valuation x x hx hx]; omega
      · rw [inverse_scale_valuation x y hx hy]; omega
      · rw [inverse_scale_valuation x z hx hz]; omega
      · exact Or.inl (by rw [inverse_scale_valuation x x hx hx]; omega)
    · refine ⟨z⁻¹,inv_ne_zero hz,?_,?_,?_,?_⟩
      · rw [inverse_scale_valuation z x hz hx]; omega
      · rw [inverse_scale_valuation z y hz hy]; omega
      · rw [inverse_scale_valuation z z hz hz]; omega
      · exact Or.inr (Or.inr (by rw [inverse_scale_valuation z z hz hz]; omega))
  · by_cases hyz : padicValRat q y≤padicValRat q z
    · refine ⟨y⁻¹,inv_ne_zero hy,?_,?_,?_,?_⟩
      · rw [inverse_scale_valuation y x hy hx]; omega
      · rw [inverse_scale_valuation y y hy hy]; omega
      · rw [inverse_scale_valuation y z hy hz]; omega
      · exact Or.inr (Or.inl (by rw [inverse_scale_valuation y y hy hy]; omega))
    · refine ⟨z⁻¹,inv_ne_zero hz,?_,?_,?_,?_⟩
      · rw [inverse_scale_valuation z x hz hx]; omega
      · rw [inverse_scale_valuation z y hz hy]; omega
      · rw [inverse_scale_valuation z z hz hz]; omega
      · exact Or.inr (Or.inr (by rw [inverse_scale_valuation z z hz hz]; omega))

noncomputable def integralOfVal (x : ℚ_[q]) (hv : 0≤x.valuation) : ℤ_[q] :=
  ⟨x,(Padic.norm_le_one_iff_val_nonneg x).mpr hv⟩

@[simp] theorem coe_integralOfVal (x : ℚ_[q]) (hv : 0≤x.valuation) :
    (integralOfVal x hv : ℚ_[q])=x := rfl

theorem integralOfVal_residue_ne_zero (x : ℚ_[q]) (hx : x ≠ 0) (hv : x.valuation=0) :
    PadicInt.toZMod (integralOfVal x (by omega)) ≠ 0 := by
  apply (padicInt_norm_eq_one_iff_residue_ne_zero _).mp
  change ‖x‖=1
  rw [Padic.norm_eq_zpow_neg_valuation hx,hv]
  simp

/-- On a smooth unit conic, two integral coordinates force the third one
integral. This is a genuine valuation inequality in the completed field. -/
theorem conic_coordinate_integral (a p b u t z : ℚ_[q])
    (ha : a ≠ 0) (hp : p ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0) (ht : t ≠ 0) (hz : z ≠ 0)
    (hva : a.valuation=0) (hvp : p.valuation=0) (hvb : b.valuation=0)
    (hvt : 0≤t.valuation) (hvz : 0≤z.valuation)
    (he : a*u^2=p*t^2-p*b*z^2) : 0≤u.valuation := by
  have hn : p*t^2+ -(p*b*z^2) ≠ 0 := by
    have hn' := mul_ne_zero ha (pow_ne_zero 2 hu)
    simpa only [he,sub_eq_add_neg] using hn'
  have hh := Padic.le_valuation_add (x:=p*t^2) (y:=-(p*b*z^2)) hn
  rw [← sub_eq_add_neg,← he,
    Padic.valuation_mul ha (pow_ne_zero _ hu),hva,
    Padic.valuation_mul hp (pow_ne_zero _ ht),hvp,
    commonRoot_val_neg,Padic.valuation_mul (mul_ne_zero hp hb) (pow_ne_zero _ hz),
    Padic.valuation_mul hp hb,hvp,hvb,zero_add,zero_add,zero_add,
    Padic.valuation_pow,Padic.valuation_pow,Padic.valuation_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  omega

#print axioms exists_primitive_rational_scale
#print axioms integralOfVal_residue_ne_zero
#print axioms conic_coordinate_integral

end FourCorner.HasseRationalNormalization
