import ActualSurvivingOrders
import OddTranslationsReplay

noncomputable section
namespace FourCorner.CommonSource
variable {q : ℕ} [Fact q.Prime]

/-- A wrong positive cyclic residue obstructs the literal return of the same
field coordinates, with integrality proved rather than assumed by a label. -/
theorem return_nonsquare_positive_cyclic (N : ℤ_[q]) (i : ZMod q)
    (hq2 : q ≠ 2) (hn : PadicInt.toZMod N ≠ 0) (hi : i^2= -1)
    {a c : ℚ_[q]}
    (ha : ∃ h : ‖a‖ ≤ 1, padicResidue a h=PadicInt.toZMod N*i)
    (hc : ∃ h : ‖c‖ ≤ 1, padicResidue c h=PadicInt.toZMod N*i)
    (hwrong : ¬ IsSquare ((1+i)/2)) : ¬ IsSquare (commonSourceReturn (N:ℚ_[q]) a c) := by
  obtain ⟨ha,har⟩ := ha
  obtain ⟨hc,hcr⟩ := hc
  have h20 : (2:ZMod q) ≠ 0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hq2)
  exact commonSource_odd_cyclic_nonsquare (padicIntegral a ha) (padicIntegral c hc)
    N i h20 hn hi har hcr hwrong

theorem return_nonsquare_negative_cyclic (N : ℤ_[q]) (i : ZMod q)
    (hq2 : q ≠ 2) (hn : PadicInt.toZMod N ≠ 0) (hi : i^2= -1)
    {a c : ℚ_[q]}
    (ha : ∃ h : ‖a‖ ≤ 1, padicResidue a h= -(PadicInt.toZMod N*i))
    (hc : ∃ h : ‖c‖ ≤ 1, padicResidue c h= -(PadicInt.toZMod N*i))
    (hwrong : ¬ IsSquare ((1-i)/2)) : ¬ IsSquare (commonSourceReturn (N:ℚ_[q]) a c) := by
  obtain ⟨ha,har⟩ := ha
  obtain ⟨hc,hcr⟩ := hc
  have h20 : (2:ZMod q) ≠ 0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hq2)
  exact commonSource_odd_cyclic_neg_nonsquare (padicIntegral a ha) (padicIntegral c hc)
    N i h20 hn hi har hcr hwrong

/-- For either surviving n=1 torsion order, two odd cyclic remainders give
exactly the negative cyclic residue. Every residue depth is retained. -/
theorem odd_remainders_wrong_return_one (N U V : ℤ_[q]) (i : ZMod q)
    (hq2 : q ≠ 2) (hn : PadicInt.toZMod N ≠ 0) (hi : i^2= -1)
    (hu : PadicInt.toZMod U=PadicInt.toZMod N*i)
    (hv : PadicInt.toZMod V=PadicInt.toZMod N*i)
    {a c : ℚ_[q]}
    (ho : (a=commonSourceTranslateMinus (N:ℚ_[q]) U ∧ c=commonSourceTranslatePlus (N:ℚ_[q]) V) ∨
      (a=commonSourceTranslatePlus (N:ℚ_[q]) U ∧ c=commonSourceTranslateMinus (N:ℚ_[q]) V))
    (hwrong : ¬ IsSquare ((1-i)/2)) : ¬ IsSquare (commonSourceReturn (N:ℚ_[q]) a c) := by
  apply return_nonsquare_negative_cyclic N i hq2 hn hi _ _ hwrong
  · rcases ho with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact commonSource_cyclic_translation_minus_residue hq2 U N i hn hi hu
    · exact commonSource_cyclic_translation_plus_residue hq2 U N i hn hi hu
  · rcases ho with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact commonSource_cyclic_translation_plus_residue hq2 V N i hn hi hv
    · exact commonSource_cyclic_translation_minus_residue hq2 V N i hn hi hv

/-- For either surviving n=7 torsion order, two odd cyclic remainders give
exactly the positive cyclic residue, for the same actual quotient. -/
theorem odd_remainders_wrong_return_seven (N U V : ℤ_[q]) (i : ZMod q)
    (hq2 : q ≠ 2) (hn : PadicInt.toZMod N ≠ 0) (hi : i^2= -1)
    (hu : PadicInt.toZMod U=PadicInt.toZMod N*i)
    (hv : PadicInt.toZMod V=PadicInt.toZMod N*i)
    {a c : ℚ_[q]}
    (ho : (a=(U:ℚ_[q]) ∧ c=(V:ℚ_[q])) ∨
      (a=commonSourceTranslateZero (N:ℚ_[q]) U ∧ c=commonSourceTranslateZero (N:ℚ_[q]) V))
    (hwrong : ¬ IsSquare ((1+i)/2)) : ¬ IsSquare (commonSourceReturn (N:ℚ_[q]) a c) := by
  apply return_nonsquare_positive_cyclic N i hq2 hn hi _ _ hwrong
  · rcases ho with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact ⟨U.property,by simpa only [padicResidue,padicIntegral,PadicInt.mk_coe] using hu⟩
    · exact commonSource_cyclic_translation_zero_residue U N i hn hi hu
  · rcases ho with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact ⟨V.property,by simpa only [padicResidue,padicIntegral,PadicInt.mk_coe] using hv⟩
    · exact commonSource_cyclic_translation_zero_residue V N i hn hi hv

#print axioms odd_remainders_wrong_return_one
#print axioms odd_remainders_wrong_return_seven
end FourCorner.CommonSource
