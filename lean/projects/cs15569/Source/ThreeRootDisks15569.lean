import CSFoundation.CommonSourceOddLocalAssembly

/-! Actual all-depth 3-adic root-disk exclusions for the literal return of
E15569. These address the two common nonzero root disks only; identifying
the original pair's reduction disks is a distinct, still missing bridge. -/
namespace FourCorner.Cs15569Completion
noncomputable section

private theorem n_residue_three : PadicInt.toZMod (15569 : ℤ_[3]) = (2 : ZMod 3) := by
  change PadicInt.toZMod ((15569 : ℕ) : ℤ_[3]) = 2
  rw [map_natCast]
  decide

private theorem n_cast_three : ((15569 : ℤ_[3]) : ℚ_[3]) = 15569 := by
  change (((15569 : ℕ) : ℤ_[3]) : ℚ_[3]) = 15569
  rw [PadicInt.coe_natCast]
  norm_num

private theorem n_norm_three : ‖(15569 : ℚ_[3])‖=1 := by
  exact Padic.norm_natCast_eq_one_iff.mpr (by norm_num)

/-- Every depth of simultaneous approach to T+ is excluded, including the
root itself. No global generator or reduction-image hypothesis enters. -/
theorem three_plus_plus {a c : ℚ_[3]}
    (ha : ‖a-15569‖<1) (hc : ‖c-15569‖<1) :
    ¬ IsSquare ((a+c)/(2*(c+15569))) := by
  have han : ‖a‖=1 :=
    (Padic.norm_eq_of_norm_sub_lt_right (by simpa [n_norm_three] using ha)).trans n_norm_three
  have hcn : ‖c‖=1 :=
    (Padic.norm_eq_of_norm_sub_lt_right (by simpa [n_norm_three] using hc)).trans n_norm_three
  let ai : ℤ_[3] := padicIntegral a han.le
  let ci : ℤ_[3] := padicIntegral c hcn.le
  exact commonSource_both_plus_nonsquare ai ci (15569 : ℤ_[3])
    (csOdd_residue_eq_of_norm_sub_lt_one ai 15569 ha)
    (csOdd_residue_eq_of_norm_sub_lt_one ci 15569 hc)
    (by rw [n_residue_three]; decide) (by decide)

/-- Every finite positive depth near T- is excluded using the actual second
ordinate e and the exact rescaling identity (2e)²f=2(a+c)c(c-n). -/
theorem three_minus_minus {a c e : ℚ_[3]}
    (ha : ‖a+15569‖<1) (hc : ‖c+15569‖<1) (he : e ≠ 0)
    (hR : e^2=c*(c-15569)*(c+15569)) :
    ¬ IsSquare ((a+c)/(2*(c+15569))) := by
  have hnn : ‖(-15569 : ℚ_[3])‖=1 := by simpa using n_norm_three
  have han : ‖a‖=1 :=
    (Padic.norm_eq_of_norm_sub_lt_right (by simpa [hnn] using ha)).trans hnn
  have hcn : ‖c‖=1 :=
    (Padic.norm_eq_of_norm_sub_lt_right (by simpa [hnn] using hc)).trans hnn
  let ai : ℤ_[3] := padicIntegral a han.le
  let ci : ℤ_[3] := padicIntegral c hcn.le
  apply commonSource_both_minus_nonsquare_of_residue ai ci (15569 : ℤ_[3]) e he hR
  · simpa only [map_neg] using csOdd_residue_eq_of_norm_sub_lt_one ai (-15569) (by simpa only [PadicInt.coe_neg, n_cast_three, sub_neg_eq_add, ai, padicIntegral] using ha)
  · simpa only [map_neg] using csOdd_residue_eq_of_norm_sub_lt_one ci (-15569) (by simpa only [PadicInt.coe_neg, n_cast_three, sub_neg_eq_add, ci, padicIntegral] using hc)
  · rw [n_residue_three]
    decide

/-- For the same actual rational second ordinate and literal f, local
squareness excludes either common nonzero-root reduction at every depth. -/
theorem rational_three_root_disks {a c e : ℚ}
    (hc : (15569 : ℚ)<c) (hR : e^2=c*(c-15569)*(c+15569))
    (hs : IsSquare (((a+c)/(2*(c+15569)) : ℚ) : ℚ_[3])) :
    ¬ ((‖(a : ℚ_[3])-15569‖<1 ∧ ‖(c : ℚ_[3])-15569‖<1) ∨
      (‖(a : ℚ_[3])+15569‖<1 ∧ ‖(c : ℚ_[3])+15569‖<1)) := by
  have he : e ≠ 0 := by
    intro hz
    have hpos : 0<c*(c-15569)*(c+15569) := by positivity
    rw [←hR,hz] at hpos
    norm_num at hpos
  have he' : (e : ℚ_[3]) ≠ 0 := by exact_mod_cast he
  have hR' : (e : ℚ_[3])^2=(c : ℚ_[3])*((c : ℚ_[3])-15569)*((c : ℚ_[3])+15569) := by
    exact_mod_cast hR
  have hs' : IsSquare (((a : ℚ_[3])+(c : ℚ_[3]))/(2*((c : ℚ_[3])+15569))) := by
    simpa using hs
  rintro (⟨ha,hc⟩ | ⟨ha,hc⟩)
  · exact three_plus_plus ha hc hs'
  · exact three_minus_minus ha hc he' hR' hs'

#print axioms three_plus_plus
#print axioms three_minus_minus
#print axioms rational_three_root_disks
end
end FourCorner.Cs15569Completion
