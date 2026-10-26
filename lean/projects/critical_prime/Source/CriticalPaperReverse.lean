import CriticalOriginalPadicReverse

/-
Copyright (c) 2026 Yuan Si. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yuan Si
-/
noncomputable section
namespace FourCorner.CriticalPadicConverse
variable {p : ℕ} [Fact p.Prime]

/-- The literal single-prime local triple in clause (iii) of `thm:crit-basic`.
The tuple is ordered by the original corners 00,10,01,11, with all roots
in the completed field and the prescribed exact valuation. -/
def PaperCriticalLocalTriple (p : ℕ) [Fact p.Prime] (s : ℕ) (X Y L : ℤ) : Prop :=
  0 < X ∧ 0 < Y ∧ X < L ∧ Y < L ∧
    Int.gcd (Int.gcd X Y : ℤ) L = 1 ∧ padicValInt p L = 2*s ∧
    ∃ A : Fin 4 → ℚ_[p], ∀ j,
      A j ^ 2 = (criticalRadicands X Y L j : ℚ_[p]) ∧
      (A j).valuation = (s : ℤ)

/-- The strict integer paper interface retains the joint primitive gcd,
all interior conditions, all four original radicands, and the same tuple. -/
theorem paper_local_reverse (hodd : p ≠ 2) (s : ℕ) (hs : 1 ≤ s)
    (X Y L : ℤ) (hlocal : PaperCriticalLocalTriple p s X Y L) :
    UnitCriticalSquarePattern p ∧ p ≠ 5 ∧ p ≠ 13 := by
  obtain ⟨_,_,_,_,hprim,hL,A,hA⟩ := hlocal
  have hg : Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs = 1 := by
    simpa only [Int.gcd_def,Int.natAbs_natCast] using hprim
  have hpat := original_padic_roots_to_unit_pattern hodd X Y L s hs A hg hL hA
  exact ⟨hpat,critical_pattern_excludes_exceptional (unitCriticalSquarePattern_to_pattern hpat)⟩

/-- A positive-depth local triple has nonzero denominator and every original
radius is nonzero, including every possible choice of its sign. -/
theorem paper_local_nonzero (s : ℕ) (hs : 1 ≤ s) (X Y L : ℤ)
    (hlocal : PaperCriticalLocalTriple p s X Y L) :
    L ≠ 0 ∧ ∃ A : Fin 4 → ℚ_[p],
      (∀ j,A j ^ 2 = (criticalRadicands X Y L j : ℚ_[p]) ∧
        (A j).valuation = (s : ℤ)) ∧ ∀ j,A j ≠ 0 := by
  obtain ⟨hX,_,hXL,_,_,_,A,hA⟩ := hlocal
  refine ⟨ne_of_gt (lt_trans hX hXL),A,hA,?_⟩
  intro j hz
  have hv := (hA j).2
  rw [hz,Padic.valuation_zero] at hv
  omega

/-- Faithful clause (iii) to clauses (ii) and (i): literal infinitude of
primitive integer triples at every depth supplies a depth-one local point.
The reverse itself works at every depth by `paper_local_reverse`. -/
theorem paper_infinite_local_reverse (hodd : p ≠ 2)
    (hlocal : ∀ s : ℕ,1 ≤ s →
      {t : ℤ × ℤ × ℤ | PaperCriticalLocalTriple p s t.1 t.2.1 t.2.2}.Infinite) :
    UnitCriticalSquarePattern p ∧ p ≠ 5 ∧ p ≠ 13 := by
  obtain ⟨t,ht⟩ := (hlocal 1 le_rfl).nonempty
  exact paper_local_reverse hodd 1 le_rfl t.1 t.2.1 t.2.2 ht

end FourCorner.CriticalPadicConverse
#print axioms FourCorner.CriticalPadicConverse.paper_local_reverse
#print axioms FourCorner.CriticalPadicConverse.paper_local_nonzero
#print axioms FourCorner.CriticalPadicConverse.paper_infinite_local_reverse
