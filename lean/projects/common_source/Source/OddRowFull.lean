import ActualCyclicOddRow
import ActualNeutralOddRow
import ActualPairPaperAdapter

noncomputable section
namespace FourCorner.CommonSource
variable {n : ℤ} {hn : n ≠ 0} {q : ℕ} [Fact q.Prime]

/-- Exactly the paper's two permitted actual whole-H probes. The cyclic
constructor retains the actual generator, double, ordered coordinate and
wrong-unit hypothesis. There is no arbitrary or assumed character. -/
inductive ActualOddProbe (n : ℤ) (hn : n ≠ 0) (q : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (hnq : (n:ZMod q) ≠ 0) where
  | neutral
      (whole : ∀ P : H n hn, reduce n hq2 hnq P=0 ∨ reduce n hq2 hnq P=residueT0 n hnq)
  | cyclic
      (A : ResiduePoint n q) (double : 2 • A=residueT0 n hnq)
      (whole : ∀ P : H n hn, reduce n hq2 hnq P ∈ AddSubgroup.zmultiples A)
      (i b : ZMod q) (coordinates : residueCoordinates A=some ((n:ZMod q)*i,b))
      (wrong1 : n%8=1 → ¬ IsSquare ((1-i)/2))
      (wrong7 : n%8=7 → ¬ IsSquare ((1+i)/2))

/-- The actual mod-four character specified by either permitted probe. -/
def ActualOddProbe.character {hq2 : q≠2} {hnq : (n:ZMod q) ≠ 0} :
    ActualOddProbe n hn q hq2 hnq → (H n hn →+ ZMod 4)
  | .neutral whole => neutralPhi hq2 hnq whole
  | .cyclic A hd whole _ _ _ _ _ =>
      Slot14.phi (H n hn) hq2 hnq A (residue_half_zero_order hnq A hd) whole

/-- The normalized cyclic abscissa is fixed by the actual chosen generator;
its existence and uniqueness do not add a probe hypothesis. -/
theorem actual_generator_coordinate_unique (hnq : (n:ZMod q) ≠ 0)
    (A : ResiduePoint n q) (hd : 2 • A=residueT0 n hnq) :
    ∃! i : ZMod q, ∃ b : ZMod q, residueCoordinates A=some ((n:ZMod q)*i,b) := by
  obtain ⟨i,b,_,hi⟩ := residue_half_zero_coordinates hnq A hd
  refine ⟨i,⟨b,hi⟩,?_⟩
  intro j hj
  obtain ⟨c,hc⟩ := hj
  exact mul_left_cancel₀ hnq (congrArg Prod.fst (Option.some.inj (hc.symm.trans hi)))

/-- Paper lem:cs-odd-row, on the exact permitted whole-H probes and complete
actual rational sources. The companion paper adapter constructs this source
from the two original ordered Kummer slots and assumed direct sum. -/
theorem common_source_odd_row (hn8 : n%8=1 ∨ n%8=7)
    (hcompl : IsCompl (H n hn) (twoTorsion (n:ℚ)))
    (W : H n hn) (hW : ActualPair.DistinguishedRow W)
    (hq : q%8=5) (hnq : (n:ZMod q) ≠ 0) (hns : IsSquare (n:ℚ_[q]))
    (probe : ActualOddProbe n hn q (by omega:q≠2) hnq) :
    parity (probe.character W)=0 ∧
      ∀ S : ActualPair n hn, IsSquare (commonSourceReturn (n:ℚ_[q]) S.a S.c) →
        probe.character S.U=probe.character S.V ∧
          (probe.character S.U=0 ∨ probe.character S.U=2) := by
  cases probe with
  | neutral whole =>
    have hWe := neutralPhi_even (by omega:q≠2) hnq whole W
    constructor
    · change parity (neutralPhi (by omega:q≠2) hnq whole W)=0
      rcases hWe with h | h <;> rw [h] <;> decide
    · intro S hf
      exact (actual_neutral_odd_row S hn8 W hq hnq hns whole hf).2
  | cyclic A hd whole i b hAi wrong1 wrong7 =>
    let hA := residue_half_zero_order hnq A hd
    have hWe := actual_cyclic_W_even hn8 hq hnq hns A hA hd whole W hW
    constructor
    · change parity (Slot14.phi (H n hn) (by omega:q≠2) hnq A hA whole W)=0
      rcases hWe with h | h <;> rw [h] <;> decide
    · intro S hf
      exact (actual_cyclic_odd_row S hn8 hcompl W hW hq hnq hns A hA hd whole i b hAi wrong1 wrong7 hf).2

#print axioms ActualOddProbe.character
#print axioms actual_generator_coordinate_unique
#print axioms common_source_odd_row
#print axioms exists_actual_pair_from_paper
end FourCorner.CommonSource
