import HSupport15569
import FourCorner.CommonRootDyadicResidues
import FourCorner.CommonRootDyadicUnitPair

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace FourCorner.Cs15569Completion
noncomputable section

theorem val_n_two : padicValRat 2 (15569 : ℚ)=0 := by
  change padicValRat 2 ((15569 : ℕ) : ℚ)=0
  rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd (by decide : ¬2 ∣ 15569)]
  rfl

theorem first_class_val_zero {d : ℤ}
    (hd : d=1 ∨ d= -1 ∨ d=15569 ∨ d= -15569) :
    padicValRat 2 (d : ℚ)=0 := by
  rcases hd with rfl | rfl | rfl | rfl
  · simp
  · simp
  · exact val_n_two
  · simpa only [Int.cast_neg,Int.cast_ofNat,padicValRat.neg] using val_n_two

/-- The globally supported classes with even valuation have no factor two. -/
theorem supported_even_first {q : ℚ} (hs : SupportedClass q)
    (hv : Even (padicValRat 2 q)) : FirstSupportedClass q := by
  obtain ⟨d,hd,u,hu,he⟩ := hs
  have hodd (D : ℚ) (hD : D ≠ 0) (hvD : padicValRat 2 D=0)
      (heq : q=(2*D)*u^2) : False := by
    have hh := congrArg (padicValRat 2) heq
    rw [padicValRat.mul (mul_ne_zero (by norm_num) hD) (pow_ne_zero _ hu.ne'),
      padicValRat.mul (by norm_num) hD,padicValRat.pow,
      show padicValRat 2 (2 : ℚ)=1 from padicValRat.self (by norm_num), hvD] at hh
    obtain ⟨k,hk⟩ := hv
    omega
  rcases hd with hd | hd | hd | hd | hd | hd | hd | hd
  · exact ⟨d,Or.inl hd,u,hu,he⟩
  · exact ⟨d,Or.inr (Or.inl hd),u,hu,he⟩
  · exact False.elim (hodd 1 (by norm_num) (by simp) (by simpa [hd] using he))
  · exact False.elim (hodd (-1) (by norm_num) (by simp) (by simpa [hd] using he))
  · exact ⟨d,Or.inr (Or.inr (Or.inl hd)),u,hu,he⟩
  · exact ⟨d,Or.inr (Or.inr (Or.inr hd)),u,hu,he⟩
  · exact False.elim (hodd 15569 (by norm_num) val_n_two (by norm_num [hd] at he ⊢; exact he))
  · exact False.elim (hodd (-15569) (by norm_num) (by simpa using val_n_two)
      (by norm_num [hd] at he ⊢; exact he))

/-- Every actual dyadic integral unit has square residue one modulo8. -/
theorem dyadic_unit_square_mod8 (a : ℤ_[2]) (ha : ‖a‖=1) :
    PadicInt.toZModPow 3 (a^2) = (1 : ZMod 8) := by
  have hunit := (dyadic_norm_one_iff_residue_ne_zero a).mp ha
  have hcast : (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2))
      (PadicInt.toZModPow 3 a) = PadicInt.toZModPow 1 a := by
    simpa only [ZMod.castHom_apply] using
      PadicInt.cast_toZModPow (p:=2) 1 3 (by decide) a
  have hfinite : ∀ r : ZMod 8,
      (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) r ≠ 0 → r^2=1 := by decide
  rw [map_pow]
  apply hfinite
  rwa [hcast]

/-- At the putative shallow depth, four times a globally supported first
slot is an integral unit with residue ±1. All denominator depths are kept. -/
theorem first_class_at_minus_two {q : ℚ} (hs : FirstSupportedClass q)
    (hv : padicValRat 2 q= -2) :
    ∃ X : ℤ_[2], (X : ℚ_[2])=4*(q : ℚ_[2]) ∧
      (PadicInt.toZModPow 3 X=1 ∨ PadicInt.toZModPow 3 X= -1) := by
  obtain ⟨d,hd,u,hu,he⟩ := hs
  have hd0 : d ≠ 0 := by rcases hd with h | h | h | h <;> rw [h] <;> norm_num
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  have hvd := first_class_val_zero hd
  have hvu : padicValRat 2 u= -1 := by
    have hh := congrArg (padicValRat 2) he
    rw [padicValRat.mul hdq (pow_ne_zero _ hu.ne'),padicValRat.pow,hvd,hv] at hh
    omega
  have hun : (u : ℚ_[2]) ≠ 0 := by exact_mod_cast hu.ne'
  have hvroot : (2*(u : ℚ_[2])).valuation=0 := by
    have htwo : (2 : ℚ_[2]).valuation=1 := by
      simpa only [Nat.cast_ofNat] using (Padic.valuation_p (p:=2))
    have hucast : (u : ℚ_[2]).valuation= -1 := by
      rw [Padic.valuation_ratCast]
      exact hvu
    rw [Padic.valuation_mul (by norm_num) hun,htwo,hucast]
    norm_num
  have hnorm : ‖2*(u : ℚ_[2])‖=1 := by
    rw [Padic.norm_eq_zpow_neg_valuation (mul_ne_zero (by norm_num) hun),hvroot]
    norm_num
  let r : ℤ_[2] := ⟨2*(u : ℚ_[2]),hnorm.le⟩
  let X : ℤ_[2] := (d : ℤ_[2])*r^2
  refine ⟨X,?_,?_⟩
  · have he' : (q : ℚ_[2])=(d : ℚ_[2])*(u : ℚ_[2])^2 := by exact_mod_cast he
    change ((d : ℤ_[2]) : ℚ_[2]) * (2*(u : ℚ_[2]))^2 = 4*(q : ℚ_[2])
    rw [PadicInt.coe_intCast,he']
    ring
  · change PadicInt.toZModPow 3 ((d : ℤ_[2])*r^2)=1 ∨
        PadicInt.toZModPow 3 ((d : ℤ_[2])*r^2)= -1
    rw [map_mul,dyadic_unit_square_mod8 r hnorm,mul_one]
    rw [map_intCast]
    rcases hd with hd | hd | hd | hd <;> rw [hd]
    · left; norm_num
    · right; norm_num
    · left; decide
    · right; decide

/-- The actual rational curve has no point with v2(x)=-2. This derives the
missing shallow-depth exclusion from global support, not from a local table
assumed complete. -/
theorem no_minus_two {x y : ℚ} (h : y^2=x*(x-15569)*(x+15569)) :
    padicValRat 2 x ≠ -2 := by
  intro hv
  have hx : x ≠ 0 := by intro hz; simp [hz] at hv
  have hn : (15569 : ℚ) ≠ 0 := by norm_num
  have hm : x-15569 ≠ 0 := by
    intro hz
    have hxv : padicValRat 2 x=0 := by rw [sub_eq_zero.mp hz]; exact val_n_two
    omega
  have hvm : padicValRat 2 (x-15569)= -2 := by
    have hh := padicValRat.add_eq_of_lt (q:=x) (r:=-(15569 : ℚ))
      (by simpa only [sub_eq_add_neg] using hm) hx (neg_ne_zero.mpr hn)
      (by rw [padicValRat.neg,hv,val_n_two]; norm_num)
    simpa only [sub_eq_add_neg,hv] using hh
  obtain ⟨X,hX,hXr⟩ := first_class_at_minus_two (first_support hx h) hv
  obtain ⟨M,hM,hMr⟩ := first_class_at_minus_two
    (supported_even_first (minus_support hm h) (by rw [hvm]; exact ⟨-1,by norm_num⟩)) hvm
  have heq : X-M=(4*15569 : ℤ_[2]) := by
    rw [show (4*15569 : ℤ_[2])=62276 by norm_num]
    change X-M=((62276 : ℕ) : ℤ_[2])
    apply PadicInt.ext
    rw [PadicInt.coe_sub,PadicInt.coe_natCast,hX,hM]
    push_cast
    ring
  have hr := congrArg (PadicInt.toZModPow 3) heq
  simp only [map_sub,map_mul,map_ofNat] at hr
  have hconst : (4*(15569 : ZMod 8))=4 := by decide
  rw [hconst] at hr
  have hfinite : ∀ r s : ZMod 8, (r=1 ∨ r= -1) → (s=1 ∨ s= -1) → r-s ≠ 4 := by decide
  exact hfinite _ _ hXr hMr hr

#print axioms supported_even_first
#print axioms first_class_at_minus_two
#print axioms no_minus_two
end
end FourCorner.Cs15569Completion
