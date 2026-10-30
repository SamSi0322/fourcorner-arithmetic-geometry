import FourCorner.HasseNormWitness
import FourCorner.CommonRootPadicVal
import FourCorner.CommonRootDyadicResidues
import FourCorner.PadicResidueSquareBasic
import Mathlib.Tactic
namespace FourCorner.HasseDyadicNorm

private instance prime2 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- In the ramified dyadic norm form the summands have opposite valuation parity,
so they never cancel, at arbitrary depths. -/
theorem norm_form_val (a b : ℚ_[2]) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a^2-2*b^2).valuation=min (2*a.valuation) (1+2*b.valuation) := by
  have ht : (2*b^2).valuation=1+2*b.valuation := by
    rw [Padic.valuation_mul (by norm_num) (pow_ne_zero _ hb),
      show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p, Padic.valuation_pow]
    simp
  rw [commonRoot_val_sub_of_ne (pow_ne_zero 2 ha)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb))
    (show (a^2).valuation ≠ (2*b^2).valuation by rw [Padic.valuation_pow,ht]; omega),
    Padic.valuation_pow,ht]
  norm_num

theorem integral_norm_coordinates (a b : ℚ_[2])
    (hn : 0 ≤ (a^2-2*b^2).valuation) : ‖a‖≤1 ∧ ‖b‖≤1 := by
  by_cases ha : a=0
  · refine ⟨by simp [ha], ?_⟩
    by_cases hb : b=0
    · simp [hb]
    have hv : (a^2-2*b^2).valuation=1+2*b.valuation := by
      simp only [ha, zero_pow (by decide : 2≠0), zero_sub, commonRoot_val_neg]
      rw [Padic.valuation_mul (by norm_num) (pow_ne_zero _ hb),
        show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p, Padic.valuation_pow]
      simp
    rw [Padic.norm_le_one_iff_val_nonneg]
    omega
  by_cases hb : b=0
  · refine ⟨?_, by simp [hb]⟩
    rw [Padic.norm_le_one_iff_val_nonneg]
    simp only [hb, zero_pow (by decide : 2≠0), mul_zero, sub_zero,
      Padic.valuation_pow] at hn
    omega
  rw [Padic.norm_le_one_iff_val_nonneg, Padic.norm_le_one_iff_val_nonneg]
  rw [norm_form_val a b ha hb] at hn
  constructor <;> omega

/-- The actual integral norm equation reduces to ±1 modulo eight when the
norm is a dyadic unit. -/
theorem unit_norm_residue (a b : ℤ_[2])
    (hu : ‖a^2-2*b^2‖=1) :
    PadicInt.toZModPow 3 (a^2-2*b^2) = 1 ∨
    PadicInt.toZModPow 3 (a^2-2*b^2) = -1 := by
  have hunit : PadicInt.toZModPow 1 (a^2-2*b^2) ≠ 0 :=
    (dyadic_norm_one_iff_residue_ne_zero _).mp hu
  have hcast : (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2))
      (PadicInt.toZModPow 3 (a^2-2*b^2)) = PadicInt.toZModPow 1 (a^2-2*b^2) := by
    simpa only [ZMod.castHom_apply] using
      PadicInt.cast_toZModPow (p := 2) 1 3 (by decide) (a^2-2*b^2)
  have hfinite : ∀ x y : ZMod 8,
      (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) (x^2-2*y^2) ≠ 0 →
      x^2-2*y^2=1 ∨ x^2-2*y^2 = -1 := by decide
  have hr := hfinite (PadicInt.toZModPow 3 a) (PadicInt.toZModPow 3 b)
  have hh : (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2))
      (PadicInt.toZModPow 3 (a^2-2*b^2)) ≠ 0 := by rw [hcast]; exact hunit
  simp only [map_sub,map_pow,map_mul,map_ofNat] at hh ⊢
  apply hr
  simpa only [map_sub,map_pow,map_mul,map_ofNat] using hh

/-- Necessary unit residue criterion for actual norms in Q2[√2]. -/
theorem actual_unit_norm_residue (x : HasseNormWitness.SqrtTwo ℚ_[2])
    (hx : x.norm ≠ 0) (hv : x.norm.valuation=0) :
    ∃ n : ℤ_[2], (n : ℚ_[2])=x.norm ∧
      (PadicInt.toZModPow 3 n=1 ∨ PadicInt.toZModPow 3 n = -1) := by
  have he : x.norm=x.re^2-2*x.im^2 := by
    simp only [QuadraticAlgebra.norm_def]; ring
  obtain ⟨ha,hb⟩ := integral_norm_coordinates x.re x.im (by rw [← he,hv])
  let a : ℤ_[2] := ⟨x.re,ha⟩
  let b : ℤ_[2] := ⟨x.im,hb⟩
  let n : ℤ_[2] := a^2-2*b^2
  have hne : (n : ℚ_[2])=x.norm := by change x.re^2-2*x.im^2=x.norm; exact he.symm
  refine ⟨n,hne,unit_norm_residue a b ?_⟩
  change ‖(n : ℚ_[2])‖=1
  rw [hne,Padic.norm_eq_zpow_neg_valuation hx,hv]
  simp
/-- Literal norm residues in Z/16; this predicate is used only as a
proved necessary finite residue condition, not as a definition of a norm. -/
def NormResidue16 (r : ZMod 16) : Prop :=
  r=0 ∨ r=1 ∨ r=2 ∨ r=4 ∨ r=7 ∨ r=8 ∨ r=9 ∨ r=12 ∨ r=14 ∨ r=15

instance (r : ZMod 16) : Decidable (NormResidue16 r) := inferInstanceAs
  (Decidable (r=0 ∨ r=1 ∨ r=2 ∨ r=4 ∨ r=7 ∨ r=8 ∨ r=9 ∨ r=12 ∨ r=14 ∨ r=15))

theorem finite_norm_residue16 (a b : ZMod 16) : NormResidue16 (a^2-2*b^2) := by
  revert a b
  decide

/-- Necessary mod-16 condition for actual integral Q2 norm values. -/
theorem actual_integral_norm_residue16 (n : ℤ_[2])
    (hn : ∃ x : HasseNormWitness.SqrtTwo ℚ_[2], x.norm=(n : ℚ_[2])) :
    NormResidue16 (PadicInt.toZModPow 4 n) := by
  obtain ⟨x,hx⟩ := hn
  have he : x.norm=x.re^2-2*x.im^2 := by
    simp only [QuadraticAlgebra.norm_def]; ring
  have hv : 0 ≤ (x.re^2-2*x.im^2).valuation := by
    rw [← he,hx,← Padic.norm_le_one_iff_val_nonneg]
    exact n.2
  obtain ⟨ha,hb⟩ := integral_norm_coordinates x.re x.im hv
  let a : ℤ_[2] := ⟨x.re,ha⟩
  let b : ℤ_[2] := ⟨x.im,hb⟩
  have hh : n=a^2-2*b^2 := by
    apply PadicInt.ext
    change (n : ℚ_[2])=x.re^2-2*x.im^2
    rw [← hx,he]
  rw [hh]
  simpa only [map_sub,map_pow,map_mul,map_ofNat] using
    finite_norm_residue16 (PadicInt.toZModPow 4 a) (PadicInt.toZModPow 4 b)

theorem three_norms_residue16 (p : ℤ_[2])
    (hp : ∃ x : HasseNormWitness.SqrtTwo ℚ_[2], x.norm=(p : ℚ_[2]))
    (ha : ∃ x : HasseNormWitness.SqrtTwo ℚ_[2], x.norm=(p : ℚ_[2])-1)
    (hb : ∃ x : HasseNormWitness.SqrtTwo ℚ_[2], x.norm=(p : ℚ_[2])+1) :
    PadicInt.toZModPow 4 p=0 ∨ PadicInt.toZModPow 4 p=1 ∨
    PadicInt.toZModPow 4 p=8 ∨ PadicInt.toZModPow 4 p=15 := by
  have hpn := actual_integral_norm_residue16 p hp
  have han := actual_integral_norm_residue16 (p-1) (by simpa using ha)
  have hbn := actual_integral_norm_residue16 (p+1) (by simpa using hb)
  simp only [map_sub,map_add,map_one] at han hbn
  have hf : ∀ r : ZMod 16, NormResidue16 r → NormResidue16 (r-1) →
      NormResidue16 (r+1) → r=0 ∨ r=1 ∨ r=8 ∨ r=15 := by decide
  exact hf _ hpn han hbn

theorem valuation_ge_of_residue_zero (n : ℤ_[2]) (hn : (n : ℚ_[2]) ≠ 0)
    (k : ℕ) (hz : PadicInt.toZModPow k n=0) :
    (k : ℤ) ≤ (n : ℚ_[2]).valuation := by
  have hh := (dyadic_residue_zero_iff_norm_le n k).mp hz
  change ‖(n : ℚ_[2])‖ ≤ _ at hh
  rw [Padic.norm_eq_zpow_neg_valuation hn] at hh
  have hv := (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hh
  omega

/-- All integral dyadic branches follow from three genuine norm witnesses
and even valuation. The norm premises still require a global argument in the paper. -/
theorem integral_three_norms_branches (p : ℤ_[2]) (hp0 : (p : ℚ_[2]) ≠ 0)
    (he : Even (p : ℚ_[2]).valuation)
    (hp : ∃ x : HasseNormWitness.SqrtTwo ℚ_[2], x.norm=(p : ℚ_[2]))
    (ha : ∃ x : HasseNormWitness.SqrtTwo ℚ_[2], x.norm=(p : ℚ_[2])-1)
    (hb : ∃ x : HasseNormWitness.SqrtTwo ℚ_[2], x.norm=(p : ℚ_[2])+1) :
    4 ≤ (p : ℚ_[2]).valuation ∨
    PadicInt.toZModPow 4 p=1 ∨ PadicInt.toZModPow 4 p=15 := by
  rcases three_norms_residue16 p hp ha hb with h0 | h1 | h8 | h15
  · exact Or.inl (valuation_ge_of_residue_zero p hp0 4 h0)
  · exact Or.inr (Or.inl h1)
  · have hz : PadicInt.toZModPow 3 p=0 := by
      have hh := PadicInt.cast_toZModPow (p:=2) 3 4 (by decide) p
      rw [h8] at hh
      norm_num at hh
      exact hh.symm
    have hv := valuation_ge_of_residue_zero p hp0 3 hz
    obtain ⟨k,hk⟩ := he
    exact Or.inl (by omega)
  · exact Or.inr (Or.inr h15)

#print axioms integral_three_norms_branches
#print axioms actual_integral_norm_residue16
#print axioms three_norms_residue16
#print axioms norm_form_val
#print axioms actual_unit_norm_residue
end FourCorner.HasseDyadicNorm
