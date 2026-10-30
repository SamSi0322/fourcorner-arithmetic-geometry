import ActualOddReturnBridge

noncomputable section
namespace FourCorner.CommonSource
open OrderedSplit
variable {n : ℤ} {hn : n ≠ 0} {q : ℕ} [Fact q.Prime]

theorem residue_half_zero_normalized_coordinate (hnq : (n:ZMod q) ≠ 0)
    (A : ResiduePoint n q) (hd : 2 • A=residueT0 n hnq) {i b : ZMod q}
    (hAi : residueCoordinates A=some ((n:ZMod q)*i,b)) : i^2= -1 := by
  obtain ⟨j,c,hj,hjc⟩ := residue_half_zero_coordinates hnq A hd
  have he : (n:ZMod q)*i=(n:ZMod q)*j :=
    congrArg Prod.fst (Option.some.inj (hAi.symm.trans hjc))
  rw [mul_left_cancel₀ hnq he]
  exact hj

/-- The actual distinguished W has an even label in the genuine whole-H cyclic
probe. The coordinate presentation and exact generator order are derived. -/
theorem actual_cyclic_W_even (hn8 : n%8=1 ∨ n%8=7)
    (hq : q%8=5) (hnq : (n:ZMod q) ≠ 0) (hns : IsSquare (n:ℚ_[q]))
    (A : ResiduePoint n q) (hA : addOrderOf A=4) (hd : 2 • A=residueT0 n hnq)
    (hwhole : ∀ P : H n hn, reduce n (by omega:q≠2) hnq P ∈ AddSubgroup.zmultiples A)
    (W : H n hn) (hW : ActualPair.DistinguishedRow W) :
    Slot14.phi (H n hn) (by omega:q≠2) hnq A hA hwhole W=0 ∨
    Slot14.phi (H n hn) (by omega:q≠2) hnq A hA hwhole W=2 := by
  rcases hn8 with h1 | h7
  · apply actual_phi_even_of_first_slot hn hq hnq hns A hA hd hwhole W (n:ℚ)
      (by exact_mod_cast hn) (hW.1 h1).1
    simpa using hns
  · apply actual_phi_even_of_first_slot hn hq hnq hns A hA hd hwhole W (-(n:ℚ))
      (by exact_mod_cast (neg_ne_zero.mpr hn)) (hW.2 h7).1
    simpa using (distinguished_local_first_slots q hq hns).2

/-- Full arithmetic assembly for the cyclic4 case of the paper odd-row lemma.
It preserves the whole H image, full source coset and the same rational pair;
there is no rank, generator-list, height or valuation-depth bound. -/
theorem actual_cyclic_odd_row (S : ActualPair n hn)
    (hn8 : n%8=1 ∨ n%8=7)
    (hcompl : IsCompl (H n hn) (twoTorsion (n:ℚ)))
    (W : H n hn) (hW : ActualPair.DistinguishedRow W)
    (hq : q%8=5) (hnq : (n:ZMod q) ≠ 0) (hns : IsSquare (n:ℚ_[q]))
    (A : ResiduePoint n q) (hA : addOrderOf A=4) (hd : 2 • A=residueT0 n hnq)
    (hwhole : ∀ P : H n hn, reduce n (by omega:q≠2) hnq P ∈ AddSubgroup.zmultiples A)
    (i b : ZMod q) (hAi : residueCoordinates A=some ((n:ZMod q)*i,b))
    (hwrong1 : n%8=1 → ¬ IsSquare ((1-i)/2))
    (hwrong7 : n%8=7 → ¬ IsSquare ((1+i)/2))
    (hfq : IsSquare (commonSourceReturn (n:ℚ_[q]) S.a S.c)) :
    let phi := Slot14.phi (H n hn) (by omega:q≠2) hnq A hA hwhole
    parity (phi W)=0 ∧ phi S.U=phi S.V ∧ (phi S.U=0 ∨ phi S.U=2) := by
  let phi := Slot14.phi (H n hn) (by omega:q≠2) hnq A hA hwhole
  have hWe : phi W=0 ∨ phi W=2 := actual_cyclic_W_even hn8 hq hnq hns A hA hd hwhole W hW
  have hWp : parity (phi W)=0 := by rcases hWe with h | h <;> rw [h] <;> decide
  obtain ⟨Z,hcoset⟩ := S.complete_coset hn8 hcompl W hW
  have hpar := labels_same_parity_from_complete_coset phi S.U S.V W Z hcoset hWe
  let r := S.remainders
  have hEven : (phi S.U=0 ∨ phi S.U=2) ∧ (phi S.V=0 ∨ phi S.V=2) := by
    rcases hpar with h | ⟨hu,hv⟩
    · exact h
    · have hi := residue_half_zero_normalized_coordinate hnq A hd hAi
      obtain ⟨yu,hyu⟩ := actual_phi_odd_abscissa hn (by omega) hnq A hA hwhole hAi S.U hu
      obtain ⟨yv,hyv⟩ := actual_phi_odd_abscissa hn (by omega) hnq A hA hwhole hAi S.V hv
      exact False.elim (actual_pair_odd_remainders_impossible S hn8 (by omega) hnq r i hi yu yv
        hyu hyv hwrong1 hwrong7 hfq)
  have hredU := (Slot14.phi_even_labels_iff (H n hn) (by omega) hnq A hA hd hwhole S.U).mp hEven.1
  have hredV := (Slot14.phi_even_labels_iff (H n hn) (by omega) hnq A hA hd hwhole S.V).mp hEven.2
  have heq : phi S.U=phi S.V := by
    apply (Slot14.phi_eq_iff (H n hn) (by omega) hnq A hA hwhole S.U S.V).mpr
    by_contra hne
    exact actual_pair_even_mismatch_impossible S hn8 hq hnq hns r hredU hredV hne hfq
  exact ⟨hWp,heq,hEven.1⟩

#print axioms actual_cyclic_W_even
#print axioms actual_cyclic_odd_row
end FourCorner.CommonSource
