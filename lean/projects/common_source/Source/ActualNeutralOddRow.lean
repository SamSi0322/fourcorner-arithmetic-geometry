import ActualOddReturnBridge

noncomputable section
namespace FourCorner.CommonSource
variable {n : ℤ} {hn : n ≠ 0} {q : ℕ} [Fact q.Prime]

@[simp] theorem residueT0_ne_zero (hnq : (n:ZMod q) ≠ 0) :
    residueT0 n hnq ≠ (0:ResiduePoint n q) :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

@[simp] theorem residueT0_add_self (hnq : (n:ZMod q) ≠ 0) :
    residueT0 n hnq+residueT0 n hnq=0 := by
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY,residueCurve,integralCurve,
    WeierstrassCurve.map,WeierstrassCurve.toAffine]

/-- The neutral probe character is 0 on O and 2 on the actual T0 reduction.
Its additivity follows from the actual reduction homomorphism and 2T0=0. -/
def neutralPhi (hq2 : q≠2) (hnq : (n:ZMod q) ≠ 0)
    (hwhole : ∀ P : H n hn, reduce n hq2 hnq P=0 ∨ reduce n hq2 hnq P=residueT0 n hnq) :
    H n hn →+ ZMod 4 := by
  classical
  refine { toFun := fun P => (if reduce n hq2 hnq P=0 then (0:ZMod 4) else 2)
           map_zero' := ?_
           map_add' := ?_ }
  · simp
  · intro P Q
    have hPQ : reduce n hq2 hnq ((P+Q : H n hn):Point (n:ℚ))=
        reduce n hq2 hnq P+reduce n hq2 hnq Q := map_add _ _ _
    rw [hPQ]
    rcases hwhole P with hp | hp <;> rcases hwhole Q with hq | hq
    <;> norm_num [hp,hq] <;> decide

@[simp] theorem neutralPhi_apply (hq2 : q≠2) (hnq : (n:ZMod q) ≠ 0)
    (hwhole : ∀ P : H n hn, reduce n hq2 hnq P=0 ∨ reduce n hq2 hnq P=residueT0 n hnq)
    (P : H n hn) : neutralPhi hq2 hnq hwhole P=
      if reduce n hq2 hnq P=0 then 0 else 2 := rfl

theorem neutralPhi_even (hq2 : q≠2) (hnq : (n:ZMod q) ≠ 0)
    (hwhole : ∀ P : H n hn, reduce n hq2 hnq P=0 ∨ reduce n hq2 hnq P=residueT0 n hnq)
    (P : H n hn) : neutralPhi hq2 hnq hwhole P=0 ∨ neutralPhi hq2 hnq hwhole P=2 := by
  classical
  rw [neutralPhi_apply]
  split_ifs <;> simp

theorem neutralPhi_eq_iff (hq2 : q≠2) (hnq : (n:ZMod q) ≠ 0)
    (hwhole : ∀ P : H n hn, reduce n hq2 hnq P=0 ∨ reduce n hq2 hnq P=residueT0 n hnq)
    (P Q : H n hn) : neutralPhi hq2 hnq hwhole P=neutralPhi hq2 hnq hwhole Q ↔
      reduce n hq2 hnq P=reduce n hq2 hnq Q := by
  classical
  rcases hwhole P with hp | hp <;> rcases hwhole Q with hq | hq
  <;> norm_num [neutralPhi_apply,hp,hq,Ne.symm (residueT0_ne_zero hnq)] <;> decide

/-- The complete neutral-probe case of the odd-row arithmetic lemma. -/
theorem actual_neutral_odd_row (S : ActualPair n hn) (hn8 : n%8=1 ∨ n%8=7)
    (W : H n hn) (hq : q%8=5) (hnq : (n:ZMod q) ≠ 0) (hns : IsSquare (n:ℚ_[q]))
    (hwhole : ∀ P : H n hn,
      reduce n (by omega:q≠2) hnq P=0 ∨ reduce n (by omega:q≠2) hnq P=residueT0 n hnq)
    (hfq : IsSquare (commonSourceReturn (n:ℚ_[q]) S.a S.c)) :
    let phi := neutralPhi (by omega:q≠2) hnq hwhole
    parity (phi W)=0 ∧ phi S.U=phi S.V ∧ (phi S.U=0 ∨ phi S.U=2) := by
  let phi := neutralPhi (by omega:q≠2) hnq hwhole
  have hW : phi W=0 ∨ phi W=2 := neutralPhi_even _ _ _ W
  have hWp : parity (phi W)=0 := by rcases hW with h | h <;> rw [h] <;> decide
  have heq : phi S.U=phi S.V := by
    apply (neutralPhi_eq_iff _ _ _ S.U S.V).mpr
    by_contra hne
    exact actual_pair_even_mismatch_impossible S hn8 hq hnq hns S.remainders
      (hwhole S.U) (hwhole S.V) hne hfq
  exact ⟨hWp,heq,neutralPhi_even _ _ _ S.U⟩

#print axioms neutralPhi
#print axioms neutralPhi_eq_iff
#print axioms actual_neutral_odd_row
end FourCorner.CommonSource
