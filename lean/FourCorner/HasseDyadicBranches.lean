import FourCorner.HasseDyadicNorm
import FourCorner.HasseDyadicSource
import FourCorner.CommonRootDyadicNormalize
namespace FourCorner.HasseDyadicBranches
private instance prime2 : Fact (Nat.Prime 2) := ⟨by decide⟩
open HasseNormWitness HasseDyadicNorm HasseDyadicSource

theorem val_zero_of_residue_one_or_fifteen (p : ℤ_[2])
    (hp : PadicInt.toZModPow 4 p=1 ∨ PadicInt.toZModPow 4 p=15) :
    (p : ℚ_[2]).valuation=0 := by
  have hh := PadicInt.cast_toZModPow (p:=2) 1 4 (by decide) p
  have hn : PadicInt.toZModPow 1 p ≠ 0 := by
    rcases hp with hp | hp
    · rw [hp] at hh
      intro hz
      exact (by decide : (ZMod.cast (1 : ZMod 16) : ZMod 2) ≠ 0) (hh.trans hz)
    · rw [hp] at hh
      intro hz
      exact (by decide : (ZMod.cast (15 : ZMod 16) : ZMod 2) ≠ 0) (hh.trans hz)
  exact (commonDyadic_unit_val ((dyadic_norm_one_iff_residue_ne_zero p).mpr hn)).2

/-- Exact four parameter branches, conditional only on the genuine three
local norm witnesses which reciprocity must supply from all other places. -/
theorem four_branches (p r : ℚ_[2])
    (hp0 : p ≠ 0) (hr0 : r ≠ 0)
    (ha0 : p-1 ≠ 0) (hb0 : p+1 ≠ 0) (hc0 : r-1 ≠ 0) (hd0 : r+1 ≠ 0)
    (h0 : IsSquare (p*r)) (h1 : IsSquare (2*(p-1)*(r-1)))
    (h2 : IsSquare (2*(p+1)*(r+1))) (h3 : IsSquare ((p-1)*r+p+1))
    (hpN : ∃ x : SqrtTwo ℚ_[2], x.norm=p)
    (haN : ∃ x : SqrtTwo ℚ_[2], x.norm=p-1)
    (hbN : ∃ x : SqrtTwo ℚ_[2], x.norm=p+1) :
    (4 ≤ p.valuation ∧ Even p.valuation) ∨
    (p.valuation ≤ -4 ∧ Even p.valuation) ∨
    (∃ P : ℤ_[2], (P : ℚ_[2])=p ∧ PadicInt.toZModPow 4 P=1) ∨
    (∃ P : ℤ_[2], (P : ℚ_[2])=p ∧ PadicInt.toZModPow 4 P=15) := by
  have he : Even p.valuation := by
    rcases valuation_dichotomy p r hp0 hr0 ha0 hb0 hc0 hd0 h0 h1 h2 h3 with hh | hh
    · exact hh.1 ▸ (show Even (0 : ℤ) from ⟨0,by simp⟩)
    · exact hh.2.2
  by_cases hnonneg : 0 ≤ p.valuation
  · let P : ℤ_[2] := ⟨p,(Padic.norm_le_one_iff_val_nonneg p).mpr hnonneg⟩
    rcases integral_three_norms_branches P hp0 he hpN haN hbN with h | h | h
    · exact Or.inl ⟨h,he⟩
    · exact Or.inr (Or.inr (Or.inl ⟨P,rfl,h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨P,rfl,h⟩))
  · have hneg : p.valuation<0 := lt_of_not_ge hnonneg
    have hq0 : 1/p ≠ 0 := div_ne_zero one_ne_zero hp0
    have hqv : (1/p).valuation= -p.valuation := by simp only [one_div,Padic.valuation_inv]
    have hqpos : 0 < (1/p).valuation := by rw [hqv]; omega
    let P : ℤ_[2] := ⟨1/p,(Padic.norm_le_one_iff_val_nonneg (1/p)).mpr hqpos.le⟩
    have hone : ∃ x : SqrtTwo ℚ_[2], x.norm=1 := ⟨1,by simp⟩
    have hpN' := exists_norm_div hp0 hone hpN
    have haN' : ∃ x : SqrtTwo ℚ_[2], x.norm=1/p-1 := by
      have hh := exists_norm_div hp0 (exists_norm_neg haN) hpN
      obtain ⟨x,hx⟩ := hh
      refine ⟨x,hx.trans ?_⟩
      field_simp
      ring
    have hbN' : ∃ x : SqrtTwo ℚ_[2], x.norm=1/p+1 := by
      have hh := exists_norm_div hp0 hbN hpN
      obtain ⟨x,hx⟩ := hh
      refine ⟨x,hx.trans ?_⟩
      field_simp
      ring
    have he' : Even (1/p).valuation := by rw [hqv]; exact he.neg
    rcases integral_three_norms_branches P hq0 he' hpN' haN' hbN' with h | h | h
    · exact Or.inr (Or.inl ⟨by change 4 ≤ (1/p).valuation at h; rw [hqv] at h; omega,he⟩)
    · have hz := val_zero_of_residue_one_or_fifteen P (Or.inl h)
      change (1/p).valuation=0 at hz
      omega
    · have hz := val_zero_of_residue_one_or_fifteen P (Or.inr h)
      change (1/p).valuation=0 at hz
      omega
#print axioms four_branches
end FourCorner.HasseDyadicBranches
