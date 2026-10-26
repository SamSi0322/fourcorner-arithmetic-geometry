import HpGoodLocal

namespace FourCorner.HpSmallResidue
open HpResidueCharts
noncomputable section
set_option maxHeartbeats 2000000

def Charts {q : ℕ} [Fact q.Prime] (p : ZMod q) : Prop :=
 (∃a : ZMod q,∃r : Fin 4 → ZMod q,∀i,r i^2=values p a i) ∨
 (∃r : Fin 3 → ZMod q,∀i,r i^2=infinityValues p p⁻¹ 0 i)

private instance prime3 : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts3 (p : ZMod 3) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 3=7 → p ≠ 3) (h11 : 3=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 3)
    change (0 : ZMod 3) ≠ 0 at hp
    change (0 : ZMod 3)-1 ≠ 0 at ha
    change (0 : ZMod 3)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 3)+1)) at hr
    change IsSquare (3-(0 : ZMod 3)) at hs
    change 3=7 → (0 : ZMod 3) ≠ 3 at h7
    change 3=11 → (0 : ZMod 3) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 3)
    change (1 : ZMod 3) ≠ 0 at hp
    change (1 : ZMod 3)-1 ≠ 0 at ha
    change (1 : ZMod 3)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 3)+1)) at hr
    change IsSquare (3-(1 : ZMod 3)) at hs
    change 3=7 → (1 : ZMod 3) ≠ 3 at h7
    change 3=11 → (1 : ZMod 3) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 3)
    change (2 : ZMod 3) ≠ 0 at hp
    change (2 : ZMod 3)-1 ≠ 0 at ha
    change (2 : ZMod 3)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 3)+1)) at hr
    change IsSquare (3-(2 : ZMod 3)) at hs
    change 3=7 → (2 : ZMod 3) ≠ 3 at h7
    change 3=11 → (2 : ZMod 3) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts3

private instance prime5 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts5 (p : ZMod 5) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 5=7 → p ≠ 3) (h11 : 5=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 5)
    change (0 : ZMod 5) ≠ 0 at hp
    change (0 : ZMod 5)-1 ≠ 0 at ha
    change (0 : ZMod 5)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 5)+1)) at hr
    change IsSquare (3-(0 : ZMod 5)) at hs
    change 5=7 → (0 : ZMod 5) ≠ 3 at h7
    change 5=11 → (0 : ZMod 5) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 5)
    change (1 : ZMod 5) ≠ 0 at hp
    change (1 : ZMod 5)-1 ≠ 0 at ha
    change (1 : ZMod 5)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 5)+1)) at hr
    change IsSquare (3-(1 : ZMod 5)) at hs
    change 5=7 → (1 : ZMod 5) ≠ 3 at h7
    change 5=11 → (1 : ZMod 5) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 5)
    change (2 : ZMod 5) ≠ 0 at hp
    change (2 : ZMod 5)-1 ≠ 0 at ha
    change (2 : ZMod 5)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 5)+1)) at hr
    change IsSquare (3-(2 : ZMod 5)) at hs
    change 5=7 → (2 : ZMod 5) ≠ 3 at h7
    change 5=11 → (2 : ZMod 5) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![1,2,2,1],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (3 : ZMod 5)
    change (3 : ZMod 5) ≠ 0 at hp
    change (3 : ZMod 5)-1 ≠ 0 at ha
    change (3 : ZMod 5)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 5)+1)) at hr
    change IsSquare (3-(3 : ZMod 5)) at hs
    change 5=7 → (3 : ZMod 5) ≠ 3 at h7
    change 5=11 → (3 : ZMod 5) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 5) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 5)
    change (4 : ZMod 5) ≠ 0 at hp
    change (4 : ZMod 5)-1 ≠ 0 at ha
    change (4 : ZMod 5)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 5)+1)) at hr
    change IsSquare (3-(4 : ZMod 5)) at hs
    change 5=7 → (4 : ZMod 5) ≠ 3 at h7
    change 5=11 → (4 : ZMod 5) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts5

private instance prime7 : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts7 (p : ZMod 7) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 7=7 → p ≠ 3) (h11 : 7=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 7)
    change (0 : ZMod 7) ≠ 0 at hp
    change (0 : ZMod 7)-1 ≠ 0 at ha
    change (0 : ZMod 7)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 7)+1)) at hr
    change IsSquare (3-(0 : ZMod 7)) at hs
    change 7=7 → (0 : ZMod 7) ≠ 3 at h7
    change 7=11 → (0 : ZMod 7) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 7)
    change (1 : ZMod 7) ≠ 0 at hp
    change (1 : ZMod 7)-1 ≠ 0 at ha
    change (1 : ZMod 7)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 7)+1)) at hr
    change IsSquare (3-(1 : ZMod 7)) at hs
    change 7=7 → (1 : ZMod 7) ≠ 3 at h7
    change 7=11 → (1 : ZMod 7) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 7)
    change (2 : ZMod 7) ≠ 0 at hp
    change (2 : ZMod 7)-1 ≠ 0 at ha
    change (2 : ZMod 7)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 7)+1)) at hr
    change IsSquare (3-(2 : ZMod 7)) at hs
    change 7=7 → (2 : ZMod 7) ≠ 3 at h7
    change 7=11 → (2 : ZMod 7) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 7) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 7)
    change (3 : ZMod 7) ≠ 0 at hp
    change (3 : ZMod 7)-1 ≠ 0 at ha
    change (3 : ZMod 7)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 7)+1)) at hr
    change IsSquare (3-(3 : ZMod 7)) at hs
    change 7=7 → (3 : ZMod 7) ≠ 3 at h7
    change 7=11 → (3 : ZMod 7) ≠ 5 at h11
    exact False.elim (h7 rfl (by decide))
  · change Charts (4 : ZMod 7)
    change (4 : ZMod 7) ≠ 0 at hp
    change (4 : ZMod 7)-1 ≠ 0 at ha
    change (4 : ZMod 7)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 7)+1)) at hr
    change IsSquare (3-(4 : ZMod 7)) at hs
    change 7=7 → (4 : ZMod 7) ≠ 3 at h7
    change 7=11 → (4 : ZMod 7) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 7) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (5 : ZMod 7)
    change (5 : ZMod 7) ≠ 0 at hp
    change (5 : ZMod 7)-1 ≠ 0 at ha
    change (5 : ZMod 7)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 7)+1)) at hr
    change IsSquare (3-(5 : ZMod 7)) at hs
    change 7=7 → (5 : ZMod 7) ≠ 3 at h7
    change 7=11 → (5 : ZMod 7) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 7) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (6 : ZMod 7)
    change (6 : ZMod 7) ≠ 0 at hp
    change (6 : ZMod 7)-1 ≠ 0 at ha
    change (6 : ZMod 7)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 7)+1)) at hr
    change IsSquare (3-(6 : ZMod 7)) at hs
    change 7=7 → (6 : ZMod 7) ≠ 3 at h7
    change 7=11 → (6 : ZMod 7) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts7

private instance prime11 : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts11 (p : ZMod 11) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 11=7 → p ≠ 3) (h11 : 11=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 11)
    change (0 : ZMod 11) ≠ 0 at hp
    change (0 : ZMod 11)-1 ≠ 0 at ha
    change (0 : ZMod 11)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 11)+1)) at hr
    change IsSquare (3-(0 : ZMod 11)) at hs
    change 11=7 → (0 : ZMod 11) ≠ 3 at h7
    change 11=11 → (0 : ZMod 11) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 11)
    change (1 : ZMod 11) ≠ 0 at hp
    change (1 : ZMod 11)-1 ≠ 0 at ha
    change (1 : ZMod 11)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 11)+1)) at hr
    change IsSquare (3-(1 : ZMod 11)) at hs
    change 11=7 → (1 : ZMod 11) ≠ 3 at h7
    change 11=11 → (1 : ZMod 11) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 11)
    change (2 : ZMod 11) ≠ 0 at hp
    change (2 : ZMod 11)-1 ≠ 0 at ha
    change (2 : ZMod 11)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 11)+1)) at hr
    change IsSquare (3-(2 : ZMod 11)) at hs
    change 11=7 → (2 : ZMod 11) ≠ 3 at h7
    change 11=11 → (2 : ZMod 11) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 11) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 11)
    change (3 : ZMod 11) ≠ 0 at hp
    change (3 : ZMod 11)-1 ≠ 0 at ha
    change (3 : ZMod 11)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 11)+1)) at hr
    change IsSquare (3-(3 : ZMod 11)) at hs
    change 11=7 → (3 : ZMod 11) ≠ 3 at h7
    change 11=11 → (3 : ZMod 11) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 11) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 11)
    change (4 : ZMod 11) ≠ 0 at hp
    change (4 : ZMod 11)-1 ≠ 0 at ha
    change (4 : ZMod 11)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 11)+1)) at hr
    change IsSquare (3-(4 : ZMod 11)) at hs
    change 11=7 → (4 : ZMod 11) ≠ 3 at h7
    change 11=11 → (4 : ZMod 11) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 11) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (5 : ZMod 11)
    change (5 : ZMod 11) ≠ 0 at hp
    change (5 : ZMod 11)-1 ≠ 0 at ha
    change (5 : ZMod 11)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 11)+1)) at hr
    change IsSquare (3-(5 : ZMod 11)) at hs
    change 11=7 → (5 : ZMod 11) ≠ 3 at h7
    change 11=11 → (5 : ZMod 11) ≠ 5 at h11
    exact False.elim (h11 rfl (by decide))
  · change Charts (6 : ZMod 11)
    change (6 : ZMod 11) ≠ 0 at hp
    change (6 : ZMod 11)-1 ≠ 0 at ha
    change (6 : ZMod 11)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 11)+1)) at hr
    change IsSquare (3-(6 : ZMod 11)) at hs
    change 11=7 → (6 : ZMod 11) ≠ 3 at h7
    change 11=11 → (6 : ZMod 11) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 11) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (7 : ZMod 11)
    change (7 : ZMod 11) ≠ 0 at hp
    change (7 : ZMod 11)-1 ≠ 0 at ha
    change (7 : ZMod 11)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 11)+1)) at hr
    change IsSquare (3-(7 : ZMod 11)) at hs
    change 11=7 → (7 : ZMod 11) ≠ 3 at h7
    change 11=11 → (7 : ZMod 11) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 11) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (8 : ZMod 11)
    change (8 : ZMod 11) ≠ 0 at hp
    change (8 : ZMod 11)-1 ≠ 0 at ha
    change (8 : ZMod 11)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 11)+1)) at hr
    change IsSquare (3-(8 : ZMod 11)) at hs
    change 11=7 → (8 : ZMod 11) ≠ 3 at h7
    change 11=11 → (8 : ZMod 11) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 11) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (9 : ZMod 11)
    change (9 : ZMod 11) ≠ 0 at hp
    change (9 : ZMod 11)-1 ≠ 0 at ha
    change (9 : ZMod 11)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 11)+1)) at hr
    change IsSquare (3-(9 : ZMod 11)) at hs
    change 11=7 → (9 : ZMod 11) ≠ 3 at h7
    change 11=11 → (9 : ZMod 11) ≠ 5 at h11
    apply Or.inl
    refine ⟨4,![5,2,1,3],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (10 : ZMod 11)
    change (10 : ZMod 11) ≠ 0 at hp
    change (10 : ZMod 11)-1 ≠ 0 at ha
    change (10 : ZMod 11)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 11)+1)) at hr
    change IsSquare (3-(10 : ZMod 11)) at hs
    change 11=7 → (10 : ZMod 11) ≠ 3 at h7
    change 11=11 → (10 : ZMod 11) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts11

private instance prime13 : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts13 (p : ZMod 13) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 13=7 → p ≠ 3) (h11 : 13=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 13)
    change (0 : ZMod 13) ≠ 0 at hp
    change (0 : ZMod 13)-1 ≠ 0 at ha
    change (0 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 13)+1)) at hr
    change IsSquare (3-(0 : ZMod 13)) at hs
    change 13=7 → (0 : ZMod 13) ≠ 3 at h7
    change 13=11 → (0 : ZMod 13) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 13)
    change (1 : ZMod 13) ≠ 0 at hp
    change (1 : ZMod 13)-1 ≠ 0 at ha
    change (1 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 13)+1)) at hr
    change IsSquare (3-(1 : ZMod 13)) at hs
    change 13=7 → (1 : ZMod 13) ≠ 3 at h7
    change 13=11 → (1 : ZMod 13) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 13)
    change (2 : ZMod 13) ≠ 0 at hp
    change (2 : ZMod 13)-1 ≠ 0 at ha
    change (2 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 13)+1)) at hr
    change IsSquare (3-(2 : ZMod 13)) at hs
    change 13=7 → (2 : ZMod 13) ≠ 3 at h7
    change 13=11 → (2 : ZMod 13) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 13) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 13)
    change (3 : ZMod 13) ≠ 0 at hp
    change (3 : ZMod 13)-1 ≠ 0 at ha
    change (3 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 13)+1)) at hr
    change IsSquare (3-(3 : ZMod 13)) at hs
    change 13=7 → (3 : ZMod 13) ≠ 3 at h7
    change 13=11 → (3 : ZMod 13) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 13) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 13)
    change (4 : ZMod 13) ≠ 0 at hp
    change (4 : ZMod 13)-1 ≠ 0 at ha
    change (4 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 13)+1)) at hr
    change IsSquare (3-(4 : ZMod 13)) at hs
    change 13=7 → (4 : ZMod 13) ≠ 3 at h7
    change 13=11 → (4 : ZMod 13) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![5,5,1,1],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (5 : ZMod 13)
    change (5 : ZMod 13) ≠ 0 at hp
    change (5 : ZMod 13)-1 ≠ 0 at ha
    change (5 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 13)+1)) at hr
    change IsSquare (3-(5 : ZMod 13)) at hs
    change 13=7 → (5 : ZMod 13) ≠ 3 at h7
    change 13=11 → (5 : ZMod 13) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 13) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (6 : ZMod 13)
    change (6 : ZMod 13) ≠ 0 at hp
    change (6 : ZMod 13)-1 ≠ 0 at ha
    change (6 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 13)+1)) at hr
    change IsSquare (3-(6 : ZMod 13)) at hs
    change 13=7 → (6 : ZMod 13) ≠ 3 at h7
    change 13=11 → (6 : ZMod 13) ≠ 5 at h11
    apply Or.inl
    refine ⟨2,![5,6,4,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (7 : ZMod 13)
    change (7 : ZMod 13) ≠ 0 at hp
    change (7 : ZMod 13)-1 ≠ 0 at ha
    change (7 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 13)+1)) at hr
    change IsSquare (3-(7 : ZMod 13)) at hs
    change 13=7 → (7 : ZMod 13) ≠ 3 at h7
    change 13=11 → (7 : ZMod 13) ≠ 5 at h11
    apply Or.inl
    refine ⟨11,![5,4,6,3],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (8 : ZMod 13)
    change (8 : ZMod 13) ≠ 0 at hp
    change (8 : ZMod 13)-1 ≠ 0 at ha
    change (8 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 13)+1)) at hr
    change IsSquare (3-(8 : ZMod 13)) at hs
    change 13=7 → (8 : ZMod 13) ≠ 3 at h7
    change 13=11 → (8 : ZMod 13) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 13) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (9 : ZMod 13)
    change (9 : ZMod 13) ≠ 0 at hp
    change (9 : ZMod 13)-1 ≠ 0 at ha
    change (9 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 13)+1)) at hr
    change IsSquare (3-(9 : ZMod 13)) at hs
    change 13=7 → (9 : ZMod 13) ≠ 3 at h7
    change 13=11 → (9 : ZMod 13) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 13) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (10 : ZMod 13)
    change (10 : ZMod 13) ≠ 0 at hp
    change (10 : ZMod 13)-1 ≠ 0 at ha
    change (10 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 13)+1)) at hr
    change IsSquare (3-(10 : ZMod 13)) at hs
    change 13=7 → (10 : ZMod 13) ≠ 3 at h7
    change 13=11 → (10 : ZMod 13) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 13) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (11 : ZMod 13)
    change (11 : ZMod 13) ≠ 0 at hp
    change (11 : ZMod 13)-1 ≠ 0 at ha
    change (11 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 13)+1)) at hr
    change IsSquare (3-(11 : ZMod 13)) at hs
    change 13=7 → (11 : ZMod 13) ≠ 3 at h7
    change 13=11 → (11 : ZMod 13) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 13) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (12 : ZMod 13)
    change (12 : ZMod 13) ≠ 0 at hp
    change (12 : ZMod 13)-1 ≠ 0 at ha
    change (12 : ZMod 13)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 13)+1)) at hr
    change IsSquare (3-(12 : ZMod 13)) at hs
    change 13=7 → (12 : ZMod 13) ≠ 3 at h7
    change 13=11 → (12 : ZMod 13) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts13

private instance prime17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts17 (p : ZMod 17) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 17=7 → p ≠ 3) (h11 : 17=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 17)
    change (0 : ZMod 17) ≠ 0 at hp
    change (0 : ZMod 17)-1 ≠ 0 at ha
    change (0 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 17)+1)) at hr
    change IsSquare (3-(0 : ZMod 17)) at hs
    change 17=7 → (0 : ZMod 17) ≠ 3 at h7
    change 17=11 → (0 : ZMod 17) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 17)
    change (1 : ZMod 17) ≠ 0 at hp
    change (1 : ZMod 17)-1 ≠ 0 at ha
    change (1 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 17)+1)) at hr
    change IsSquare (3-(1 : ZMod 17)) at hs
    change 17=7 → (1 : ZMod 17) ≠ 3 at h7
    change 17=11 → (1 : ZMod 17) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 17)
    change (2 : ZMod 17) ≠ 0 at hp
    change (2 : ZMod 17)-1 ≠ 0 at ha
    change (2 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 17)+1)) at hr
    change IsSquare (3-(2 : ZMod 17)) at hs
    change 17=7 → (2 : ZMod 17) ≠ 3 at h7
    change 17=11 → (2 : ZMod 17) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 17) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 17)
    change (3 : ZMod 17) ≠ 0 at hp
    change (3 : ZMod 17)-1 ≠ 0 at ha
    change (3 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 17)+1)) at hr
    change IsSquare (3-(3 : ZMod 17)) at hs
    change 17=7 → (3 : ZMod 17) ≠ 3 at h7
    change 17=11 → (3 : ZMod 17) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,8,5,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (4 : ZMod 17)
    change (4 : ZMod 17) ≠ 0 at hp
    change (4 : ZMod 17)-1 ≠ 0 at ha
    change (4 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 17)+1)) at hr
    change IsSquare (3-(4 : ZMod 17)) at hs
    change 17=7 → (4 : ZMod 17) ≠ 3 at h7
    change 17=11 → (4 : ZMod 17) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 17) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (5 : ZMod 17)
    change (5 : ZMod 17) ≠ 0 at hp
    change (5 : ZMod 17)-1 ≠ 0 at ha
    change (5 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 17)+1)) at hr
    change IsSquare (3-(5 : ZMod 17)) at hs
    change 17=7 → (5 : ZMod 17) ≠ 3 at h7
    change 17=11 → (5 : ZMod 17) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 17) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (6 : ZMod 17)
    change (6 : ZMod 17) ≠ 0 at hp
    change (6 : ZMod 17)-1 ≠ 0 at ha
    change (6 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 17)+1)) at hr
    change IsSquare (3-(6 : ZMod 17)) at hs
    change 17=7 → (6 : ZMod 17) ≠ 3 at h7
    change 17=11 → (6 : ZMod 17) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 17) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 17)
    change (7 : ZMod 17) ≠ 0 at hp
    change (7 : ZMod 17)-1 ≠ 0 at ha
    change (7 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 17)+1)) at hr
    change IsSquare (3-(7 : ZMod 17)) at hs
    change 17=7 → (7 : ZMod 17) ≠ 3 at h7
    change 17=11 → (7 : ZMod 17) ≠ 5 at h11
    apply Or.inl
    refine ⟨7,![7,2,3,4],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (8 : ZMod 17)
    change (8 : ZMod 17) ≠ 0 at hp
    change (8 : ZMod 17)-1 ≠ 0 at ha
    change (8 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 17)+1)) at hr
    change IsSquare (3-(8 : ZMod 17)) at hs
    change 17=7 → (8 : ZMod 17) ≠ 3 at h7
    change 17=11 → (8 : ZMod 17) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 17) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (9 : ZMod 17)
    change (9 : ZMod 17) ≠ 0 at hp
    change (9 : ZMod 17)-1 ≠ 0 at ha
    change (9 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 17)+1)) at hr
    change IsSquare (3-(9 : ZMod 17)) at hs
    change 17=7 → (9 : ZMod 17) ≠ 3 at h7
    change 17=11 → (9 : ZMod 17) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 17) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (10 : ZMod 17)
    change (10 : ZMod 17) ≠ 0 at hp
    change (10 : ZMod 17)-1 ≠ 0 at ha
    change (10 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 17)+1)) at hr
    change IsSquare (3-(10 : ZMod 17)) at hs
    change 17=7 → (10 : ZMod 17) ≠ 3 at h7
    change 17=11 → (10 : ZMod 17) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 17) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 17)
    change (11 : ZMod 17) ≠ 0 at hp
    change (11 : ZMod 17)-1 ≠ 0 at ha
    change (11 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 17)+1)) at hr
    change IsSquare (3-(11 : ZMod 17)) at hs
    change 17=7 → (11 : ZMod 17) ≠ 3 at h7
    change 17=11 → (11 : ZMod 17) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 17) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (12 : ZMod 17)
    change (12 : ZMod 17) ≠ 0 at hp
    change (12 : ZMod 17)-1 ≠ 0 at ha
    change (12 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 17)+1)) at hr
    change IsSquare (3-(12 : ZMod 17)) at hs
    change 17=7 → (12 : ZMod 17) ≠ 3 at h7
    change 17=11 → (12 : ZMod 17) ≠ 5 at h11
    apply Or.inl
    refine ⟨12,![5,2,7,3],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (13 : ZMod 17)
    change (13 : ZMod 17) ≠ 0 at hp
    change (13 : ZMod 17)-1 ≠ 0 at ha
    change (13 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 17)+1)) at hr
    change IsSquare (3-(13 : ZMod 17)) at hs
    change 17=7 → (13 : ZMod 17) ≠ 3 at h7
    change 17=11 → (13 : ZMod 17) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 17) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (14 : ZMod 17)
    change (14 : ZMod 17) ≠ 0 at hp
    change (14 : ZMod 17)-1 ≠ 0 at ha
    change (14 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 17)+1)) at hr
    change IsSquare (3-(14 : ZMod 17)) at hs
    change 17=7 → (14 : ZMod 17) ≠ 3 at h7
    change 17=11 → (14 : ZMod 17) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 17) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (15 : ZMod 17)
    change (15 : ZMod 17) ≠ 0 at hp
    change (15 : ZMod 17)-1 ≠ 0 at ha
    change (15 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 17)+1)) at hr
    change IsSquare (3-(15 : ZMod 17)) at hs
    change 17=7 → (15 : ZMod 17) ≠ 3 at h7
    change 17=11 → (15 : ZMod 17) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 17) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (16 : ZMod 17)
    change (16 : ZMod 17) ≠ 0 at hp
    change (16 : ZMod 17)-1 ≠ 0 at ha
    change (16 : ZMod 17)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 17)+1)) at hr
    change IsSquare (3-(16 : ZMod 17)) at hs
    change 17=7 → (16 : ZMod 17) ≠ 3 at h7
    change 17=11 → (16 : ZMod 17) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts17

private instance prime19 : Fact (Nat.Prime 19) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts19 (p : ZMod 19) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 19=7 → p ≠ 3) (h11 : 19=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 19)
    change (0 : ZMod 19) ≠ 0 at hp
    change (0 : ZMod 19)-1 ≠ 0 at ha
    change (0 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 19)+1)) at hr
    change IsSquare (3-(0 : ZMod 19)) at hs
    change 19=7 → (0 : ZMod 19) ≠ 3 at h7
    change 19=11 → (0 : ZMod 19) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 19)
    change (1 : ZMod 19) ≠ 0 at hp
    change (1 : ZMod 19)-1 ≠ 0 at ha
    change (1 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 19)+1)) at hr
    change IsSquare (3-(1 : ZMod 19)) at hs
    change 19=7 → (1 : ZMod 19) ≠ 3 at h7
    change 19=11 → (1 : ZMod 19) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 19)
    change (2 : ZMod 19) ≠ 0 at hp
    change (2 : ZMod 19)-1 ≠ 0 at ha
    change (2 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 19)+1)) at hr
    change IsSquare (3-(2 : ZMod 19)) at hs
    change 19=7 → (2 : ZMod 19) ≠ 3 at h7
    change 19=11 → (2 : ZMod 19) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![5,2,9,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (3 : ZMod 19)
    change (3 : ZMod 19) ≠ 0 at hp
    change (3 : ZMod 19)-1 ≠ 0 at ha
    change (3 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 19)+1)) at hr
    change IsSquare (3-(3 : ZMod 19)) at hs
    change 19=7 → (3 : ZMod 19) ≠ 3 at h7
    change 19=11 → (3 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 19)
    change (4 : ZMod 19) ≠ 0 at hp
    change (4 : ZMod 19)-1 ≠ 0 at ha
    change (4 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 19)+1)) at hr
    change IsSquare (3-(4 : ZMod 19)) at hs
    change 19=7 → (4 : ZMod 19) ≠ 3 at h7
    change 19=11 → (4 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (5 : ZMod 19)
    change (5 : ZMod 19) ≠ 0 at hp
    change (5 : ZMod 19)-1 ≠ 0 at ha
    change (5 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 19)+1)) at hr
    change IsSquare (3-(5 : ZMod 19)) at hs
    change 19=7 → (5 : ZMod 19) ≠ 3 at h7
    change 19=11 → (5 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (6 : ZMod 19)
    change (6 : ZMod 19) ≠ 0 at hp
    change (6 : ZMod 19)-1 ≠ 0 at ha
    change (6 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 19)+1)) at hr
    change IsSquare (3-(6 : ZMod 19)) at hs
    change 19=7 → (6 : ZMod 19) ≠ 3 at h7
    change 19=11 → (6 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 19)
    change (7 : ZMod 19) ≠ 0 at hp
    change (7 : ZMod 19)-1 ≠ 0 at ha
    change (7 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 19)+1)) at hr
    change IsSquare (3-(7 : ZMod 19)) at hs
    change 19=7 → (7 : ZMod 19) ≠ 3 at h7
    change 19=11 → (7 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (8 : ZMod 19)
    change (8 : ZMod 19) ≠ 0 at hp
    change (8 : ZMod 19)-1 ≠ 0 at ha
    change (8 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 19)+1)) at hr
    change IsSquare (3-(8 : ZMod 19)) at hs
    change 19=7 → (8 : ZMod 19) ≠ 3 at h7
    change 19=11 → (8 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (9 : ZMod 19)
    change (9 : ZMod 19) ≠ 0 at hp
    change (9 : ZMod 19)-1 ≠ 0 at ha
    change (9 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 19)+1)) at hr
    change IsSquare (3-(9 : ZMod 19)) at hs
    change 19=7 → (9 : ZMod 19) ≠ 3 at h7
    change 19=11 → (9 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (10 : ZMod 19)
    change (10 : ZMod 19) ≠ 0 at hp
    change (10 : ZMod 19)-1 ≠ 0 at ha
    change (10 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 19)+1)) at hr
    change IsSquare (3-(10 : ZMod 19)) at hs
    change 19=7 → (10 : ZMod 19) ≠ 3 at h7
    change 19=11 → (10 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 19)
    change (11 : ZMod 19) ≠ 0 at hp
    change (11 : ZMod 19)-1 ≠ 0 at ha
    change (11 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 19)+1)) at hr
    change IsSquare (3-(11 : ZMod 19)) at hs
    change 19=7 → (11 : ZMod 19) ≠ 3 at h7
    change 19=11 → (11 : ZMod 19) ≠ 5 at h11
    apply Or.inl
    refine ⟨5,![6,2,7,9],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (12 : ZMod 19)
    change (12 : ZMod 19) ≠ 0 at hp
    change (12 : ZMod 19)-1 ≠ 0 at ha
    change (12 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 19)+1)) at hr
    change IsSquare (3-(12 : ZMod 19)) at hs
    change 19=7 → (12 : ZMod 19) ≠ 3 at h7
    change 19=11 → (12 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (13 : ZMod 19)
    change (13 : ZMod 19) ≠ 0 at hp
    change (13 : ZMod 19)-1 ≠ 0 at ha
    change (13 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 19)+1)) at hr
    change IsSquare (3-(13 : ZMod 19)) at hs
    change 19=7 → (13 : ZMod 19) ≠ 3 at h7
    change 19=11 → (13 : ZMod 19) ≠ 5 at h11
    apply Or.inl
    refine ⟨10,![4,8,2,1],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (14 : ZMod 19)
    change (14 : ZMod 19) ≠ 0 at hp
    change (14 : ZMod 19)-1 ≠ 0 at ha
    change (14 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 19)+1)) at hr
    change IsSquare (3-(14 : ZMod 19)) at hs
    change 19=7 → (14 : ZMod 19) ≠ 3 at h7
    change 19=11 → (14 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (15 : ZMod 19)
    change (15 : ZMod 19) ≠ 0 at hp
    change (15 : ZMod 19)-1 ≠ 0 at ha
    change (15 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 19)+1)) at hr
    change IsSquare (3-(15 : ZMod 19)) at hs
    change 19=7 → (15 : ZMod 19) ≠ 3 at h7
    change 19=11 → (15 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (16 : ZMod 19)
    change (16 : ZMod 19) ≠ 0 at hp
    change (16 : ZMod 19)-1 ≠ 0 at ha
    change (16 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 19)+1)) at hr
    change IsSquare (3-(16 : ZMod 19)) at hs
    change 19=7 → (16 : ZMod 19) ≠ 3 at h7
    change 19=11 → (16 : ZMod 19) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 19) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 19)
    change (17 : ZMod 19) ≠ 0 at hp
    change (17 : ZMod 19)-1 ≠ 0 at ha
    change (17 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 19)+1)) at hr
    change IsSquare (3-(17 : ZMod 19)) at hs
    change 19=7 → (17 : ZMod 19) ≠ 3 at h7
    change 19=11 → (17 : ZMod 19) ≠ 5 at h11
    apply Or.inl
    refine ⟨4,![7,1,3,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (18 : ZMod 19)
    change (18 : ZMod 19) ≠ 0 at hp
    change (18 : ZMod 19)-1 ≠ 0 at ha
    change (18 : ZMod 19)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 19)+1)) at hr
    change IsSquare (3-(18 : ZMod 19)) at hs
    change 19=7 → (18 : ZMod 19) ≠ 3 at h7
    change 19=11 → (18 : ZMod 19) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts19

private instance prime23 : Fact (Nat.Prime 23) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts23 (p : ZMod 23) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 23=7 → p ≠ 3) (h11 : 23=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 23)
    change (0 : ZMod 23) ≠ 0 at hp
    change (0 : ZMod 23)-1 ≠ 0 at ha
    change (0 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 23)+1)) at hr
    change IsSquare (3-(0 : ZMod 23)) at hs
    change 23=7 → (0 : ZMod 23) ≠ 3 at h7
    change 23=11 → (0 : ZMod 23) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 23)
    change (1 : ZMod 23) ≠ 0 at hp
    change (1 : ZMod 23)-1 ≠ 0 at ha
    change (1 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 23)+1)) at hr
    change IsSquare (3-(1 : ZMod 23)) at hs
    change 23=7 → (1 : ZMod 23) ≠ 3 at h7
    change 23=11 → (1 : ZMod 23) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 23)
    change (2 : ZMod 23) ≠ 0 at hp
    change (2 : ZMod 23)-1 ≠ 0 at ha
    change (2 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 23)+1)) at hr
    change IsSquare (3-(2 : ZMod 23)) at hs
    change 23=7 → (2 : ZMod 23) ≠ 3 at h7
    change 23=11 → (2 : ZMod 23) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![5,0,9,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (3 : ZMod 23)
    change (3 : ZMod 23) ≠ 0 at hp
    change (3 : ZMod 23)-1 ≠ 0 at ha
    change (3 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 23)+1)) at hr
    change IsSquare (3-(3 : ZMod 23)) at hs
    change 23=7 → (3 : ZMod 23) ≠ 3 at h7
    change 23=11 → (3 : ZMod 23) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![7,0,4,11],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (4 : ZMod 23)
    change (4 : ZMod 23) ≠ 0 at hp
    change (4 : ZMod 23)-1 ≠ 0 at ha
    change (4 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 23)+1)) at hr
    change IsSquare (3-(4 : ZMod 23)) at hs
    change 23=7 → (4 : ZMod 23) ≠ 3 at h7
    change 23=11 → (4 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (5 : ZMod 23)
    change (5 : ZMod 23) ≠ 0 at hp
    change (5 : ZMod 23)-1 ≠ 0 at ha
    change (5 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 23)+1)) at hr
    change IsSquare (3-(5 : ZMod 23)) at hs
    change 23=7 → (5 : ZMod 23) ≠ 3 at h7
    change 23=11 → (5 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (6 : ZMod 23)
    change (6 : ZMod 23) ≠ 0 at hp
    change (6 : ZMod 23)-1 ≠ 0 at ha
    change (6 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 23)+1)) at hr
    change IsSquare (3-(6 : ZMod 23)) at hs
    change 23=7 → (6 : ZMod 23) ≠ 3 at h7
    change 23=11 → (6 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 23)
    change (7 : ZMod 23) ≠ 0 at hp
    change (7 : ZMod 23)-1 ≠ 0 at ha
    change (7 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 23)+1)) at hr
    change IsSquare (3-(7 : ZMod 23)) at hs
    change 23=7 → (7 : ZMod 23) ≠ 3 at h7
    change 23=11 → (7 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (8 : ZMod 23)
    change (8 : ZMod 23) ≠ 0 at hp
    change (8 : ZMod 23)-1 ≠ 0 at ha
    change (8 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 23)+1)) at hr
    change IsSquare (3-(8 : ZMod 23)) at hs
    change 23=7 → (8 : ZMod 23) ≠ 3 at h7
    change 23=11 → (8 : ZMod 23) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,3,8,3],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (9 : ZMod 23)
    change (9 : ZMod 23) ≠ 0 at hp
    change (9 : ZMod 23)-1 ≠ 0 at ha
    change (9 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 23)+1)) at hr
    change IsSquare (3-(9 : ZMod 23)) at hs
    change 23=7 → (9 : ZMod 23) ≠ 3 at h7
    change 23=11 → (9 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (10 : ZMod 23)
    change (10 : ZMod 23) ≠ 0 at hp
    change (10 : ZMod 23)-1 ≠ 0 at ha
    change (10 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 23)+1)) at hr
    change IsSquare (3-(10 : ZMod 23)) at hs
    change 23=7 → (10 : ZMod 23) ≠ 3 at h7
    change 23=11 → (10 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 23)
    change (11 : ZMod 23) ≠ 0 at hp
    change (11 : ZMod 23)-1 ≠ 0 at ha
    change (11 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 23)+1)) at hr
    change IsSquare (3-(11 : ZMod 23)) at hs
    change 23=7 → (11 : ZMod 23) ≠ 3 at h7
    change 23=11 → (11 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (12 : ZMod 23)
    change (12 : ZMod 23) ≠ 0 at hp
    change (12 : ZMod 23)-1 ≠ 0 at ha
    change (12 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 23)+1)) at hr
    change IsSquare (3-(12 : ZMod 23)) at hs
    change 23=7 → (12 : ZMod 23) ≠ 3 at h7
    change 23=11 → (12 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (13 : ZMod 23)
    change (13 : ZMod 23) ≠ 0 at hp
    change (13 : ZMod 23)-1 ≠ 0 at ha
    change (13 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 23)+1)) at hr
    change IsSquare (3-(13 : ZMod 23)) at hs
    change 23=7 → (13 : ZMod 23) ≠ 3 at h7
    change 23=11 → (13 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (14 : ZMod 23)
    change (14 : ZMod 23) ≠ 0 at hp
    change (14 : ZMod 23)-1 ≠ 0 at ha
    change (14 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 23)+1)) at hr
    change IsSquare (3-(14 : ZMod 23)) at hs
    change 23=7 → (14 : ZMod 23) ≠ 3 at h7
    change 23=11 → (14 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 23)
    change (15 : ZMod 23) ≠ 0 at hp
    change (15 : ZMod 23)-1 ≠ 0 at ha
    change (15 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 23)+1)) at hr
    change IsSquare (3-(15 : ZMod 23)) at hs
    change 23=7 → (15 : ZMod 23) ≠ 3 at h7
    change 23=11 → (15 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (16 : ZMod 23)
    change (16 : ZMod 23) ≠ 0 at hp
    change (16 : ZMod 23)-1 ≠ 0 at ha
    change (16 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 23)+1)) at hr
    change IsSquare (3-(16 : ZMod 23)) at hs
    change 23=7 → (16 : ZMod 23) ≠ 3 at h7
    change 23=11 → (16 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 23)
    change (17 : ZMod 23) ≠ 0 at hp
    change (17 : ZMod 23)-1 ≠ 0 at ha
    change (17 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 23)+1)) at hr
    change IsSquare (3-(17 : ZMod 23)) at hs
    change 23=7 → (17 : ZMod 23) ≠ 3 at h7
    change 23=11 → (17 : ZMod 23) ≠ 5 at h11
    apply Or.inl
    refine ⟨5,![4,6,3,11],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (18 : ZMod 23)
    change (18 : ZMod 23) ≠ 0 at hp
    change (18 : ZMod 23)-1 ≠ 0 at ha
    change (18 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 23)+1)) at hr
    change IsSquare (3-(18 : ZMod 23)) at hs
    change 23=7 → (18 : ZMod 23) ≠ 3 at h7
    change 23=11 → (18 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (19 : ZMod 23)
    change (19 : ZMod 23) ≠ 0 at hp
    change (19 : ZMod 23)-1 ≠ 0 at ha
    change (19 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 23)+1)) at hr
    change IsSquare (3-(19 : ZMod 23)) at hs
    change 23=7 → (19 : ZMod 23) ≠ 3 at h7
    change 23=11 → (19 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (20 : ZMod 23)
    change (20 : ZMod 23) ≠ 0 at hp
    change (20 : ZMod 23)-1 ≠ 0 at ha
    change (20 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 23)+1)) at hr
    change IsSquare (3-(20 : ZMod 23)) at hs
    change 23=7 → (20 : ZMod 23) ≠ 3 at h7
    change 23=11 → (20 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (21 : ZMod 23)
    change (21 : ZMod 23) ≠ 0 at hp
    change (21 : ZMod 23)-1 ≠ 0 at ha
    change (21 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 23)+1)) at hr
    change IsSquare (3-(21 : ZMod 23)) at hs
    change 23=7 → (21 : ZMod 23) ≠ 3 at h7
    change 23=11 → (21 : ZMod 23) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 23) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (22 : ZMod 23)
    change (22 : ZMod 23) ≠ 0 at hp
    change (22 : ZMod 23)-1 ≠ 0 at ha
    change (22 : ZMod 23)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 23)+1)) at hr
    change IsSquare (3-(22 : ZMod 23)) at hs
    change 23=7 → (22 : ZMod 23) ≠ 3 at h7
    change 23=11 → (22 : ZMod 23) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts23

private instance prime29 : Fact (Nat.Prime 29) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts29 (p : ZMod 29) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 29=7 → p ≠ 3) (h11 : 29=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 29)
    change (0 : ZMod 29) ≠ 0 at hp
    change (0 : ZMod 29)-1 ≠ 0 at ha
    change (0 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 29)+1)) at hr
    change IsSquare (3-(0 : ZMod 29)) at hs
    change 29=7 → (0 : ZMod 29) ≠ 3 at h7
    change 29=11 → (0 : ZMod 29) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 29)
    change (1 : ZMod 29) ≠ 0 at hp
    change (1 : ZMod 29)-1 ≠ 0 at ha
    change (1 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 29)+1)) at hr
    change IsSquare (3-(1 : ZMod 29)) at hs
    change 29=7 → (1 : ZMod 29) ≠ 3 at h7
    change 29=11 → (1 : ZMod 29) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 29)
    change (2 : ZMod 29) ≠ 0 at hp
    change (2 : ZMod 29)-1 ≠ 0 at ha
    change (2 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 29)+1)) at hr
    change IsSquare (3-(2 : ZMod 29)) at hs
    change 29=7 → (2 : ZMod 29) ≠ 3 at h7
    change 29=11 → (2 : ZMod 29) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![8,2,13,8],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (3 : ZMod 29)
    change (3 : ZMod 29) ≠ 0 at hp
    change (3 : ZMod 29)-1 ≠ 0 at ha
    change (3 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 29)+1)) at hr
    change IsSquare (3-(3 : ZMod 29)) at hs
    change 29=7 → (3 : ZMod 29) ≠ 3 at h7
    change 29=11 → (3 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 29)
    change (4 : ZMod 29) ≠ 0 at hp
    change (4 : ZMod 29)-1 ≠ 0 at ha
    change (4 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 29)+1)) at hr
    change IsSquare (3-(4 : ZMod 29)) at hs
    change 29=7 → (4 : ZMod 29) ≠ 3 at h7
    change 29=11 → (4 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (5 : ZMod 29)
    change (5 : ZMod 29) ≠ 0 at hp
    change (5 : ZMod 29)-1 ≠ 0 at ha
    change (5 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 29)+1)) at hr
    change IsSquare (3-(5 : ZMod 29)) at hs
    change 29=7 → (5 : ZMod 29) ≠ 3 at h7
    change 29=11 → (5 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (6 : ZMod 29)
    change (6 : ZMod 29) ≠ 0 at hp
    change (6 : ZMod 29)-1 ≠ 0 at ha
    change (6 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 29)+1)) at hr
    change IsSquare (3-(6 : ZMod 29)) at hs
    change 29=7 → (6 : ZMod 29) ≠ 3 at h7
    change 29=11 → (6 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 29)
    change (7 : ZMod 29) ≠ 0 at hp
    change (7 : ZMod 29)-1 ≠ 0 at ha
    change (7 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 29)+1)) at hr
    change IsSquare (3-(7 : ZMod 29)) at hs
    change 29=7 → (7 : ZMod 29) ≠ 3 at h7
    change 29=11 → (7 : ZMod 29) ≠ 5 at h11
    apply Or.inl
    refine ⟨22,![3,7,7,13],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (8 : ZMod 29)
    change (8 : ZMod 29) ≠ 0 at hp
    change (8 : ZMod 29)-1 ≠ 0 at ha
    change (8 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 29)+1)) at hr
    change IsSquare (3-(8 : ZMod 29)) at hs
    change 29=7 → (8 : ZMod 29) ≠ 3 at h7
    change 29=11 → (8 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (9 : ZMod 29)
    change (9 : ZMod 29) ≠ 0 at hp
    change (9 : ZMod 29)-1 ≠ 0 at ha
    change (9 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 29)+1)) at hr
    change IsSquare (3-(9 : ZMod 29)) at hs
    change 29=7 → (9 : ZMod 29) ≠ 3 at h7
    change 29=11 → (9 : ZMod 29) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![5,14,13,0],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (10 : ZMod 29)
    change (10 : ZMod 29) ≠ 0 at hp
    change (10 : ZMod 29)-1 ≠ 0 at ha
    change (10 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 29)+1)) at hr
    change IsSquare (3-(10 : ZMod 29)) at hs
    change 29=7 → (10 : ZMod 29) ≠ 3 at h7
    change 29=11 → (10 : ZMod 29) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![1,6,1,3],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (11 : ZMod 29)
    change (11 : ZMod 29) ≠ 0 at hp
    change (11 : ZMod 29)-1 ≠ 0 at ha
    change (11 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 29)+1)) at hr
    change IsSquare (3-(11 : ZMod 29)) at hs
    change 29=7 → (11 : ZMod 29) ≠ 3 at h7
    change 29=11 → (11 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (12 : ZMod 29)
    change (12 : ZMod 29) ≠ 0 at hp
    change (12 : ZMod 29)-1 ≠ 0 at ha
    change (12 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 29)+1)) at hr
    change IsSquare (3-(12 : ZMod 29)) at hs
    change 29=7 → (12 : ZMod 29) ≠ 3 at h7
    change 29=11 → (12 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (13 : ZMod 29)
    change (13 : ZMod 29) ≠ 0 at hp
    change (13 : ZMod 29)-1 ≠ 0 at ha
    change (13 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 29)+1)) at hr
    change IsSquare (3-(13 : ZMod 29)) at hs
    change 29=7 → (13 : ZMod 29) ≠ 3 at h7
    change 29=11 → (13 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (14 : ZMod 29)
    change (14 : ZMod 29) ≠ 0 at hp
    change (14 : ZMod 29)-1 ≠ 0 at ha
    change (14 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 29)+1)) at hr
    change IsSquare (3-(14 : ZMod 29)) at hs
    change 29=7 → (14 : ZMod 29) ≠ 3 at h7
    change 29=11 → (14 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (15 : ZMod 29)
    change (15 : ZMod 29) ≠ 0 at hp
    change (15 : ZMod 29)-1 ≠ 0 at ha
    change (15 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 29)+1)) at hr
    change IsSquare (3-(15 : ZMod 29)) at hs
    change 29=7 → (15 : ZMod 29) ≠ 3 at h7
    change 29=11 → (15 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (16 : ZMod 29)
    change (16 : ZMod 29) ≠ 0 at hp
    change (16 : ZMod 29)-1 ≠ 0 at ha
    change (16 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 29)+1)) at hr
    change IsSquare (3-(16 : ZMod 29)) at hs
    change 29=7 → (16 : ZMod 29) ≠ 3 at h7
    change 29=11 → (16 : ZMod 29) ≠ 5 at h11
    apply Or.inl
    refine ⟨5,![14,2,1,11],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (17 : ZMod 29)
    change (17 : ZMod 29) ≠ 0 at hp
    change (17 : ZMod 29)-1 ≠ 0 at ha
    change (17 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 29)+1)) at hr
    change IsSquare (3-(17 : ZMod 29)) at hs
    change 29=7 → (17 : ZMod 29) ≠ 3 at h7
    change 29=11 → (17 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (18 : ZMod 29)
    change (18 : ZMod 29) ≠ 0 at hp
    change (18 : ZMod 29)-1 ≠ 0 at ha
    change (18 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 29)+1)) at hr
    change IsSquare (3-(18 : ZMod 29)) at hs
    change 29=7 → (18 : ZMod 29) ≠ 3 at h7
    change 29=11 → (18 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (19 : ZMod 29)
    change (19 : ZMod 29) ≠ 0 at hp
    change (19 : ZMod 29)-1 ≠ 0 at ha
    change (19 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 29)+1)) at hr
    change IsSquare (3-(19 : ZMod 29)) at hs
    change 29=7 → (19 : ZMod 29) ≠ 3 at h7
    change 29=11 → (19 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (20 : ZMod 29)
    change (20 : ZMod 29) ≠ 0 at hp
    change (20 : ZMod 29)-1 ≠ 0 at ha
    change (20 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 29)+1)) at hr
    change IsSquare (3-(20 : ZMod 29)) at hs
    change 29=7 → (20 : ZMod 29) ≠ 3 at h7
    change 29=11 → (20 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (21 : ZMod 29)
    change (21 : ZMod 29) ≠ 0 at hp
    change (21 : ZMod 29)-1 ≠ 0 at ha
    change (21 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 29)+1)) at hr
    change IsSquare (3-(21 : ZMod 29)) at hs
    change 29=7 → (21 : ZMod 29) ≠ 3 at h7
    change 29=11 → (21 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (22 : ZMod 29)
    change (22 : ZMod 29) ≠ 0 at hp
    change (22 : ZMod 29)-1 ≠ 0 at ha
    change (22 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 29)+1)) at hr
    change IsSquare (3-(22 : ZMod 29)) at hs
    change 29=7 → (22 : ZMod 29) ≠ 3 at h7
    change 29=11 → (22 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (23 : ZMod 29)
    change (23 : ZMod 29) ≠ 0 at hp
    change (23 : ZMod 29)-1 ≠ 0 at ha
    change (23 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 29)+1)) at hr
    change IsSquare (3-(23 : ZMod 29)) at hs
    change 29=7 → (23 : ZMod 29) ≠ 3 at h7
    change 29=11 → (23 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (24 : ZMod 29)
    change (24 : ZMod 29) ≠ 0 at hp
    change (24 : ZMod 29)-1 ≠ 0 at ha
    change (24 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 29)+1)) at hr
    change IsSquare (3-(24 : ZMod 29)) at hs
    change 29=7 → (24 : ZMod 29) ≠ 3 at h7
    change 29=11 → (24 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (25 : ZMod 29)
    change (25 : ZMod 29) ≠ 0 at hp
    change (25 : ZMod 29)-1 ≠ 0 at ha
    change (25 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 29)+1)) at hr
    change IsSquare (3-(25 : ZMod 29)) at hs
    change 29=7 → (25 : ZMod 29) ≠ 3 at h7
    change 29=11 → (25 : ZMod 29) ≠ 5 at h11
    apply Or.inl
    refine ⟨4,![10,12,12,8],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (26 : ZMod 29)
    change (26 : ZMod 29) ≠ 0 at hp
    change (26 : ZMod 29)-1 ≠ 0 at ha
    change (26 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 29)+1)) at hr
    change IsSquare (3-(26 : ZMod 29)) at hs
    change 29=7 → (26 : ZMod 29) ≠ 3 at h7
    change 29=11 → (26 : ZMod 29) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![10,2,9,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (27 : ZMod 29)
    change (27 : ZMod 29) ≠ 0 at hp
    change (27 : ZMod 29)-1 ≠ 0 at ha
    change (27 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 29)+1)) at hr
    change IsSquare (3-(27 : ZMod 29)) at hs
    change 29=7 → (27 : ZMod 29) ≠ 3 at h7
    change 29=11 → (27 : ZMod 29) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 29) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (28 : ZMod 29)
    change (28 : ZMod 29) ≠ 0 at hp
    change (28 : ZMod 29)-1 ≠ 0 at ha
    change (28 : ZMod 29)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 29)+1)) at hr
    change IsSquare (3-(28 : ZMod 29)) at hs
    change 29=7 → (28 : ZMod 29) ≠ 3 at h7
    change 29=11 → (28 : ZMod 29) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts29

private instance prime31 : Fact (Nat.Prime 31) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts31 (p : ZMod 31) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 31=7 → p ≠ 3) (h11 : 31=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 31)
    change (0 : ZMod 31) ≠ 0 at hp
    change (0 : ZMod 31)-1 ≠ 0 at ha
    change (0 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 31)+1)) at hr
    change IsSquare (3-(0 : ZMod 31)) at hs
    change 31=7 → (0 : ZMod 31) ≠ 3 at h7
    change 31=11 → (0 : ZMod 31) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 31)
    change (1 : ZMod 31) ≠ 0 at hp
    change (1 : ZMod 31)-1 ≠ 0 at ha
    change (1 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 31)+1)) at hr
    change IsSquare (3-(1 : ZMod 31)) at hs
    change 31=7 → (1 : ZMod 31) ≠ 3 at h7
    change 31=11 → (1 : ZMod 31) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 31)
    change (2 : ZMod 31) ≠ 0 at hp
    change (2 : ZMod 31)-1 ≠ 0 at ha
    change (2 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 31)+1)) at hr
    change IsSquare (3-(2 : ZMod 31)) at hs
    change 31=7 → (2 : ZMod 31) ≠ 3 at h7
    change 31=11 → (2 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 31)
    change (3 : ZMod 31) ≠ 0 at hp
    change (3 : ZMod 31)-1 ≠ 0 at ha
    change (3 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 31)+1)) at hr
    change IsSquare (3-(3 : ZMod 31)) at hs
    change 31=7 → (3 : ZMod 31) ≠ 3 at h7
    change 31=11 → (3 : ZMod 31) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![3,15,1,14],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (4 : ZMod 31)
    change (4 : ZMod 31) ≠ 0 at hp
    change (4 : ZMod 31)-1 ≠ 0 at ha
    change (4 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 31)+1)) at hr
    change IsSquare (3-(4 : ZMod 31)) at hs
    change 31=7 → (4 : ZMod 31) ≠ 3 at h7
    change 31=11 → (4 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (5 : ZMod 31)
    change (5 : ZMod 31) ≠ 0 at hp
    change (5 : ZMod 31)-1 ≠ 0 at ha
    change (5 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 31)+1)) at hr
    change IsSquare (3-(5 : ZMod 31)) at hs
    change 31=7 → (5 : ZMod 31) ≠ 3 at h7
    change 31=11 → (5 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (6 : ZMod 31)
    change (6 : ZMod 31) ≠ 0 at hp
    change (6 : ZMod 31)-1 ≠ 0 at ha
    change (6 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 31)+1)) at hr
    change IsSquare (3-(6 : ZMod 31)) at hs
    change 31=7 → (6 : ZMod 31) ≠ 3 at h7
    change 31=11 → (6 : ZMod 31) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![11,4,10,12],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (7 : ZMod 31)
    change (7 : ZMod 31) ≠ 0 at hp
    change (7 : ZMod 31)-1 ≠ 0 at ha
    change (7 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 31)+1)) at hr
    change IsSquare (3-(7 : ZMod 31)) at hs
    change 31=7 → (7 : ZMod 31) ≠ 3 at h7
    change 31=11 → (7 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (8 : ZMod 31)
    change (8 : ZMod 31) ≠ 0 at hp
    change (8 : ZMod 31)-1 ≠ 0 at ha
    change (8 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 31)+1)) at hr
    change IsSquare (3-(8 : ZMod 31)) at hs
    change 31=7 → (8 : ZMod 31) ≠ 3 at h7
    change 31=11 → (8 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (9 : ZMod 31)
    change (9 : ZMod 31) ≠ 0 at hp
    change (9 : ZMod 31)-1 ≠ 0 at ha
    change (9 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 31)+1)) at hr
    change IsSquare (3-(9 : ZMod 31)) at hs
    change 31=7 → (9 : ZMod 31) ≠ 3 at h7
    change 31=11 → (9 : ZMod 31) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![3,0,3,7],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (10 : ZMod 31)
    change (10 : ZMod 31) ≠ 0 at hp
    change (10 : ZMod 31)-1 ≠ 0 at ha
    change (10 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 31)+1)) at hr
    change IsSquare (3-(10 : ZMod 31)) at hs
    change 31=7 → (10 : ZMod 31) ≠ 3 at h7
    change 31=11 → (10 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 31)
    change (11 : ZMod 31) ≠ 0 at hp
    change (11 : ZMod 31)-1 ≠ 0 at ha
    change (11 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 31)+1)) at hr
    change IsSquare (3-(11 : ZMod 31)) at hs
    change 31=7 → (11 : ZMod 31) ≠ 3 at h7
    change 31=11 → (11 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (12 : ZMod 31)
    change (12 : ZMod 31) ≠ 0 at hp
    change (12 : ZMod 31)-1 ≠ 0 at ha
    change (12 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 31)+1)) at hr
    change IsSquare (3-(12 : ZMod 31)) at hs
    change 31=7 → (12 : ZMod 31) ≠ 3 at h7
    change 31=11 → (12 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (13 : ZMod 31)
    change (13 : ZMod 31) ≠ 0 at hp
    change (13 : ZMod 31)-1 ≠ 0 at ha
    change (13 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 31)+1)) at hr
    change IsSquare (3-(13 : ZMod 31)) at hs
    change 31=7 → (13 : ZMod 31) ≠ 3 at h7
    change 31=11 → (13 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (14 : ZMod 31)
    change (14 : ZMod 31) ≠ 0 at hp
    change (14 : ZMod 31)-1 ≠ 0 at ha
    change (14 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 31)+1)) at hr
    change IsSquare (3-(14 : ZMod 31)) at hs
    change 31=7 → (14 : ZMod 31) ≠ 3 at h7
    change 31=11 → (14 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 31)
    change (15 : ZMod 31) ≠ 0 at hp
    change (15 : ZMod 31)-1 ≠ 0 at ha
    change (15 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 31)+1)) at hr
    change IsSquare (3-(15 : ZMod 31)) at hs
    change 31=7 → (15 : ZMod 31) ≠ 3 at h7
    change 31=11 → (15 : ZMod 31) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![11,4,10,10],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (16 : ZMod 31)
    change (16 : ZMod 31) ≠ 0 at hp
    change (16 : ZMod 31)-1 ≠ 0 at ha
    change (16 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 31)+1)) at hr
    change IsSquare (3-(16 : ZMod 31)) at hs
    change 31=7 → (16 : ZMod 31) ≠ 3 at h7
    change 31=11 → (16 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 31)
    change (17 : ZMod 31) ≠ 0 at hp
    change (17 : ZMod 31)-1 ≠ 0 at ha
    change (17 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 31)+1)) at hr
    change IsSquare (3-(17 : ZMod 31)) at hs
    change 31=7 → (17 : ZMod 31) ≠ 3 at h7
    change 31=11 → (17 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (18 : ZMod 31)
    change (18 : ZMod 31) ≠ 0 at hp
    change (18 : ZMod 31)-1 ≠ 0 at ha
    change (18 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 31)+1)) at hr
    change IsSquare (3-(18 : ZMod 31)) at hs
    change 31=7 → (18 : ZMod 31) ≠ 3 at h7
    change 31=11 → (18 : ZMod 31) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,11,10,9],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (19 : ZMod 31)
    change (19 : ZMod 31) ≠ 0 at hp
    change (19 : ZMod 31)-1 ≠ 0 at ha
    change (19 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 31)+1)) at hr
    change IsSquare (3-(19 : ZMod 31)) at hs
    change 31=7 → (19 : ZMod 31) ≠ 3 at h7
    change 31=11 → (19 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (20 : ZMod 31)
    change (20 : ZMod 31) ≠ 0 at hp
    change (20 : ZMod 31)-1 ≠ 0 at ha
    change (20 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 31)+1)) at hr
    change IsSquare (3-(20 : ZMod 31)) at hs
    change 31=7 → (20 : ZMod 31) ≠ 3 at h7
    change 31=11 → (20 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (21 : ZMod 31)
    change (21 : ZMod 31) ≠ 0 at hp
    change (21 : ZMod 31)-1 ≠ 0 at ha
    change (21 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 31)+1)) at hr
    change IsSquare (3-(21 : ZMod 31)) at hs
    change 31=7 → (21 : ZMod 31) ≠ 3 at h7
    change 31=11 → (21 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (22 : ZMod 31)
    change (22 : ZMod 31) ≠ 0 at hp
    change (22 : ZMod 31)-1 ≠ 0 at ha
    change (22 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 31)+1)) at hr
    change IsSquare (3-(22 : ZMod 31)) at hs
    change 31=7 → (22 : ZMod 31) ≠ 3 at h7
    change 31=11 → (22 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (23 : ZMod 31)
    change (23 : ZMod 31) ≠ 0 at hp
    change (23 : ZMod 31)-1 ≠ 0 at ha
    change (23 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 31)+1)) at hr
    change IsSquare (3-(23 : ZMod 31)) at hs
    change 31=7 → (23 : ZMod 31) ≠ 3 at h7
    change 31=11 → (23 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (24 : ZMod 31)
    change (24 : ZMod 31) ≠ 0 at hp
    change (24 : ZMod 31)-1 ≠ 0 at ha
    change (24 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 31)+1)) at hr
    change IsSquare (3-(24 : ZMod 31)) at hs
    change 31=7 → (24 : ZMod 31) ≠ 3 at h7
    change 31=11 → (24 : ZMod 31) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,4,9,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (25 : ZMod 31)
    change (25 : ZMod 31) ≠ 0 at hp
    change (25 : ZMod 31)-1 ≠ 0 at ha
    change (25 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 31)+1)) at hr
    change IsSquare (3-(25 : ZMod 31)) at hs
    change 31=7 → (25 : ZMod 31) ≠ 3 at h7
    change 31=11 → (25 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (26 : ZMod 31)
    change (26 : ZMod 31) ≠ 0 at hp
    change (26 : ZMod 31)-1 ≠ 0 at ha
    change (26 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 31)+1)) at hr
    change IsSquare (3-(26 : ZMod 31)) at hs
    change 31=7 → (26 : ZMod 31) ≠ 3 at h7
    change 31=11 → (26 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (27 : ZMod 31)
    change (27 : ZMod 31) ≠ 0 at hp
    change (27 : ZMod 31)-1 ≠ 0 at ha
    change (27 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 31)+1)) at hr
    change IsSquare (3-(27 : ZMod 31)) at hs
    change 31=7 → (27 : ZMod 31) ≠ 3 at h7
    change 31=11 → (27 : ZMod 31) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,14,5,11],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (28 : ZMod 31)
    change (28 : ZMod 31) ≠ 0 at hp
    change (28 : ZMod 31)-1 ≠ 0 at ha
    change (28 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 31)+1)) at hr
    change IsSquare (3-(28 : ZMod 31)) at hs
    change 31=7 → (28 : ZMod 31) ≠ 3 at h7
    change 31=11 → (28 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (29 : ZMod 31)
    change (29 : ZMod 31) ≠ 0 at hp
    change (29 : ZMod 31)-1 ≠ 0 at ha
    change (29 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 31)+1)) at hr
    change IsSquare (3-(29 : ZMod 31)) at hs
    change 31=7 → (29 : ZMod 31) ≠ 3 at h7
    change 31=11 → (29 : ZMod 31) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 31) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (30 : ZMod 31)
    change (30 : ZMod 31) ≠ 0 at hp
    change (30 : ZMod 31)-1 ≠ 0 at ha
    change (30 : ZMod 31)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 31)+1)) at hr
    change IsSquare (3-(30 : ZMod 31)) at hs
    change 31=7 → (30 : ZMod 31) ≠ 3 at h7
    change 31=11 → (30 : ZMod 31) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts31

private instance prime37 : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts37 (p : ZMod 37) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 37=7 → p ≠ 3) (h11 : 37=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 37)
    change (0 : ZMod 37) ≠ 0 at hp
    change (0 : ZMod 37)-1 ≠ 0 at ha
    change (0 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 37)+1)) at hr
    change IsSquare (3-(0 : ZMod 37)) at hs
    change 37=7 → (0 : ZMod 37) ≠ 3 at h7
    change 37=11 → (0 : ZMod 37) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 37)
    change (1 : ZMod 37) ≠ 0 at hp
    change (1 : ZMod 37)-1 ≠ 0 at ha
    change (1 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 37)+1)) at hr
    change IsSquare (3-(1 : ZMod 37)) at hs
    change 37=7 → (1 : ZMod 37) ≠ 3 at h7
    change 37=11 → (1 : ZMod 37) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 37)
    change (2 : ZMod 37) ≠ 0 at hp
    change (2 : ZMod 37)-1 ≠ 0 at ha
    change (2 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 37)+1)) at hr
    change IsSquare (3-(2 : ZMod 37)) at hs
    change 37=7 → (2 : ZMod 37) ≠ 3 at h7
    change 37=11 → (2 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 37)
    change (3 : ZMod 37) ≠ 0 at hp
    change (3 : ZMod 37)-1 ≠ 0 at ha
    change (3 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 37)+1)) at hr
    change IsSquare (3-(3 : ZMod 37)) at hs
    change 37=7 → (3 : ZMod 37) ≠ 3 at h7
    change 37=11 → (3 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 37)
    change (4 : ZMod 37) ≠ 0 at hp
    change (4 : ZMod 37)-1 ≠ 0 at ha
    change (4 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 37)+1)) at hr
    change IsSquare (3-(4 : ZMod 37)) at hs
    change 37=7 → (4 : ZMod 37) ≠ 3 at h7
    change 37=11 → (4 : ZMod 37) ≠ 5 at h11
    apply Or.inl
    refine ⟨33,![13,9,9,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (5 : ZMod 37)
    change (5 : ZMod 37) ≠ 0 at hp
    change (5 : ZMod 37)-1 ≠ 0 at ha
    change (5 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 37)+1)) at hr
    change IsSquare (3-(5 : ZMod 37)) at hs
    change 37=7 → (5 : ZMod 37) ≠ 3 at h7
    change 37=11 → (5 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (6 : ZMod 37)
    change (6 : ZMod 37) ≠ 0 at hp
    change (6 : ZMod 37)-1 ≠ 0 at ha
    change (6 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 37)+1)) at hr
    change IsSquare (3-(6 : ZMod 37)) at hs
    change 37=7 → (6 : ZMod 37) ≠ 3 at h7
    change 37=11 → (6 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 37)
    change (7 : ZMod 37) ≠ 0 at hp
    change (7 : ZMod 37)-1 ≠ 0 at ha
    change (7 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 37)+1)) at hr
    change IsSquare (3-(7 : ZMod 37)) at hs
    change 37=7 → (7 : ZMod 37) ≠ 3 at h7
    change 37=11 → (7 : ZMod 37) ≠ 5 at h11
    apply Or.inl
    refine ⟨11,![15,3,9,0],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (8 : ZMod 37)
    change (8 : ZMod 37) ≠ 0 at hp
    change (8 : ZMod 37)-1 ≠ 0 at ha
    change (8 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 37)+1)) at hr
    change IsSquare (3-(8 : ZMod 37)) at hs
    change 37=7 → (8 : ZMod 37) ≠ 3 at h7
    change 37=11 → (8 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (9 : ZMod 37)
    change (9 : ZMod 37) ≠ 0 at hp
    change (9 : ZMod 37)-1 ≠ 0 at ha
    change (9 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 37)+1)) at hr
    change IsSquare (3-(9 : ZMod 37)) at hs
    change 37=7 → (9 : ZMod 37) ≠ 3 at h7
    change 37=11 → (9 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (10 : ZMod 37)
    change (10 : ZMod 37) ≠ 0 at hp
    change (10 : ZMod 37)-1 ≠ 0 at ha
    change (10 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 37)+1)) at hr
    change IsSquare (3-(10 : ZMod 37)) at hs
    change 37=7 → (10 : ZMod 37) ≠ 3 at h7
    change 37=11 → (10 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 37)
    change (11 : ZMod 37) ≠ 0 at hp
    change (11 : ZMod 37)-1 ≠ 0 at ha
    change (11 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 37)+1)) at hr
    change IsSquare (3-(11 : ZMod 37)) at hs
    change 37=7 → (11 : ZMod 37) ≠ 3 at h7
    change 37=11 → (11 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (12 : ZMod 37)
    change (12 : ZMod 37) ≠ 0 at hp
    change (12 : ZMod 37)-1 ≠ 0 at ha
    change (12 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 37)+1)) at hr
    change IsSquare (3-(12 : ZMod 37)) at hs
    change 37=7 → (12 : ZMod 37) ≠ 3 at h7
    change 37=11 → (12 : ZMod 37) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![6,9,17,3],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (13 : ZMod 37)
    change (13 : ZMod 37) ≠ 0 at hp
    change (13 : ZMod 37)-1 ≠ 0 at ha
    change (13 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 37)+1)) at hr
    change IsSquare (3-(13 : ZMod 37)) at hs
    change 37=7 → (13 : ZMod 37) ≠ 3 at h7
    change 37=11 → (13 : ZMod 37) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![2,3,14,7],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (14 : ZMod 37)
    change (14 : ZMod 37) ≠ 0 at hp
    change (14 : ZMod 37)-1 ≠ 0 at ha
    change (14 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 37)+1)) at hr
    change IsSquare (3-(14 : ZMod 37)) at hs
    change 37=7 → (14 : ZMod 37) ≠ 3 at h7
    change 37=11 → (14 : ZMod 37) ≠ 5 at h11
    apply Or.inl
    refine ⟨2,![18,10,4,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (15 : ZMod 37)
    change (15 : ZMod 37) ≠ 0 at hp
    change (15 : ZMod 37)-1 ≠ 0 at ha
    change (15 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 37)+1)) at hr
    change IsSquare (3-(15 : ZMod 37)) at hs
    change 37=7 → (15 : ZMod 37) ≠ 3 at h7
    change 37=11 → (15 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (32 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (16 : ZMod 37)
    change (16 : ZMod 37) ≠ 0 at hp
    change (16 : ZMod 37)-1 ≠ 0 at ha
    change (16 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 37)+1)) at hr
    change IsSquare (3-(16 : ZMod 37)) at hs
    change 37=7 → (16 : ZMod 37) ≠ 3 at h7
    change 37=11 → (16 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (17 : ZMod 37)
    change (17 : ZMod 37) ≠ 0 at hp
    change (17 : ZMod 37)-1 ≠ 0 at ha
    change (17 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 37)+1)) at hr
    change IsSquare (3-(17 : ZMod 37)) at hs
    change 37=7 → (17 : ZMod 37) ≠ 3 at h7
    change 37=11 → (17 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (18 : ZMod 37)
    change (18 : ZMod 37) ≠ 0 at hp
    change (18 : ZMod 37)-1 ≠ 0 at ha
    change (18 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 37)+1)) at hr
    change IsSquare (3-(18 : ZMod 37)) at hs
    change 37=7 → (18 : ZMod 37) ≠ 3 at h7
    change 37=11 → (18 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (19 : ZMod 37)
    change (19 : ZMod 37) ≠ 0 at hp
    change (19 : ZMod 37)-1 ≠ 0 at ha
    change (19 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 37)+1)) at hr
    change IsSquare (3-(19 : ZMod 37)) at hs
    change 37=7 → (19 : ZMod 37) ≠ 3 at h7
    change 37=11 → (19 : ZMod 37) ≠ 5 at h11
    apply Or.inl
    refine ⟨8,![2,17,8,4],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (20 : ZMod 37)
    change (20 : ZMod 37) ≠ 0 at hp
    change (20 : ZMod 37)-1 ≠ 0 at ha
    change (20 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 37)+1)) at hr
    change IsSquare (3-(20 : ZMod 37)) at hs
    change 37=7 → (20 : ZMod 37) ≠ 3 at h7
    change 37=11 → (20 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (21 : ZMod 37)
    change (21 : ZMod 37) ≠ 0 at hp
    change (21 : ZMod 37)-1 ≠ 0 at ha
    change (21 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 37)+1)) at hr
    change IsSquare (3-(21 : ZMod 37)) at hs
    change 37=7 → (21 : ZMod 37) ≠ 3 at h7
    change 37=11 → (21 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (22 : ZMod 37)
    change (22 : ZMod 37) ≠ 0 at hp
    change (22 : ZMod 37)-1 ≠ 0 at ha
    change (22 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 37)+1)) at hr
    change IsSquare (3-(22 : ZMod 37)) at hs
    change 37=7 → (22 : ZMod 37) ≠ 3 at h7
    change 37=11 → (22 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (23 : ZMod 37)
    change (23 : ZMod 37) ≠ 0 at hp
    change (23 : ZMod 37)-1 ≠ 0 at ha
    change (23 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 37)+1)) at hr
    change IsSquare (3-(23 : ZMod 37)) at hs
    change 37=7 → (23 : ZMod 37) ≠ 3 at h7
    change 37=11 → (23 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (24 : ZMod 37)
    change (24 : ZMod 37) ≠ 0 at hp
    change (24 : ZMod 37)-1 ≠ 0 at ha
    change (24 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 37)+1)) at hr
    change IsSquare (3-(24 : ZMod 37)) at hs
    change 37=7 → (24 : ZMod 37) ≠ 3 at h7
    change 37=11 → (24 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (25 : ZMod 37)
    change (25 : ZMod 37) ≠ 0 at hp
    change (25 : ZMod 37)-1 ≠ 0 at ha
    change (25 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 37)+1)) at hr
    change IsSquare (3-(25 : ZMod 37)) at hs
    change 37=7 → (25 : ZMod 37) ≠ 3 at h7
    change 37=11 → (25 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (26 : ZMod 37)
    change (26 : ZMod 37) ≠ 0 at hp
    change (26 : ZMod 37)-1 ≠ 0 at ha
    change (26 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 37)+1)) at hr
    change IsSquare (3-(26 : ZMod 37)) at hs
    change 37=7 → (26 : ZMod 37) ≠ 3 at h7
    change 37=11 → (26 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (27 : ZMod 37)
    change (27 : ZMod 37) ≠ 0 at hp
    change (27 : ZMod 37)-1 ≠ 0 at ha
    change (27 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 37)+1)) at hr
    change IsSquare (3-(27 : ZMod 37)) at hs
    change 37=7 → (27 : ZMod 37) ≠ 3 at h7
    change 37=11 → (27 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (28 : ZMod 37)
    change (28 : ZMod 37) ≠ 0 at hp
    change (28 : ZMod 37)-1 ≠ 0 at ha
    change (28 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 37)+1)) at hr
    change IsSquare (3-(28 : ZMod 37)) at hs
    change 37=7 → (28 : ZMod 37) ≠ 3 at h7
    change 37=11 → (28 : ZMod 37) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![11,16,11,6],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (29 : ZMod 37)
    change (29 : ZMod 37) ≠ 0 at hp
    change (29 : ZMod 37)-1 ≠ 0 at ha
    change (29 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 37)+1)) at hr
    change IsSquare (3-(29 : ZMod 37)) at hs
    change 37=7 → (29 : ZMod 37) ≠ 3 at h7
    change 37=11 → (29 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (30 : ZMod 37)
    change (30 : ZMod 37) ≠ 0 at hp
    change (30 : ZMod 37)-1 ≠ 0 at ha
    change (30 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 37)+1)) at hr
    change IsSquare (3-(30 : ZMod 37)) at hs
    change 37=7 → (30 : ZMod 37) ≠ 3 at h7
    change 37=11 → (30 : ZMod 37) ≠ 5 at h11
    apply Or.inl
    refine ⟨10,![2,2,4,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (31 : ZMod 37)
    change (31 : ZMod 37) ≠ 0 at hp
    change (31 : ZMod 37)-1 ≠ 0 at ha
    change (31 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 37)+1)) at hr
    change IsSquare (3-(31 : ZMod 37)) at hs
    change 37=7 → (31 : ZMod 37) ≠ 3 at h7
    change 37=11 → (31 : ZMod 37) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![1,2,2,8],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (32 : ZMod 37)
    change (32 : ZMod 37) ≠ 0 at hp
    change (32 : ZMod 37)-1 ≠ 0 at ha
    change (32 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 37)+1)) at hr
    change IsSquare (3-(32 : ZMod 37)) at hs
    change 37=7 → (32 : ZMod 37) ≠ 3 at h7
    change 37=11 → (32 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (33 : ZMod 37)
    change (33 : ZMod 37) ≠ 0 at hp
    change (33 : ZMod 37)-1 ≠ 0 at ha
    change (33 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 37)+1)) at hr
    change IsSquare (3-(33 : ZMod 37)) at hs
    change 37=7 → (33 : ZMod 37) ≠ 3 at h7
    change 37=11 → (33 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (34 : ZMod 37)
    change (34 : ZMod 37) ≠ 0 at hp
    change (34 : ZMod 37)-1 ≠ 0 at ha
    change (34 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 37)+1)) at hr
    change IsSquare (3-(34 : ZMod 37)) at hs
    change 37=7 → (34 : ZMod 37) ≠ 3 at h7
    change 37=11 → (34 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (35 : ZMod 37)
    change (35 : ZMod 37) ≠ 0 at hp
    change (35 : ZMod 37)-1 ≠ 0 at ha
    change (35 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 37)+1)) at hr
    change IsSquare (3-(35 : ZMod 37)) at hs
    change 37=7 → (35 : ZMod 37) ≠ 3 at h7
    change 37=11 → (35 : ZMod 37) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 37) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (36 : ZMod 37)
    change (36 : ZMod 37) ≠ 0 at hp
    change (36 : ZMod 37)-1 ≠ 0 at ha
    change (36 : ZMod 37)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 37)+1)) at hr
    change IsSquare (3-(36 : ZMod 37)) at hs
    change 37=7 → (36 : ZMod 37) ≠ 3 at h7
    change 37=11 → (36 : ZMod 37) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts37

private instance prime41 : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts41 (p : ZMod 41) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 41=7 → p ≠ 3) (h11 : 41=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 41)
    change (0 : ZMod 41) ≠ 0 at hp
    change (0 : ZMod 41)-1 ≠ 0 at ha
    change (0 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 41)+1)) at hr
    change IsSquare (3-(0 : ZMod 41)) at hs
    change 41=7 → (0 : ZMod 41) ≠ 3 at h7
    change 41=11 → (0 : ZMod 41) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 41)
    change (1 : ZMod 41) ≠ 0 at hp
    change (1 : ZMod 41)-1 ≠ 0 at ha
    change (1 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 41)+1)) at hr
    change IsSquare (3-(1 : ZMod 41)) at hs
    change 41=7 → (1 : ZMod 41) ≠ 3 at h7
    change 41=11 → (1 : ZMod 41) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 41)
    change (2 : ZMod 41) ≠ 0 at hp
    change (2 : ZMod 41)-1 ≠ 0 at ha
    change (2 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 41)+1)) at hr
    change IsSquare (3-(2 : ZMod 41)) at hs
    change 41=7 → (2 : ZMod 41) ≠ 3 at h7
    change 41=11 → (2 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 41)
    change (3 : ZMod 41) ≠ 0 at hp
    change (3 : ZMod 41)-1 ≠ 0 at ha
    change (3 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 41)+1)) at hr
    change IsSquare (3-(3 : ZMod 41)) at hs
    change 41=7 → (3 : ZMod 41) ≠ 3 at h7
    change 41=11 → (3 : ZMod 41) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,18,7,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (4 : ZMod 41)
    change (4 : ZMod 41) ≠ 0 at hp
    change (4 : ZMod 41)-1 ≠ 0 at ha
    change (4 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 41)+1)) at hr
    change IsSquare (3-(4 : ZMod 41)) at hs
    change 41=7 → (4 : ZMod 41) ≠ 3 at h7
    change 41=11 → (4 : ZMod 41) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![2,0,15,7],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (5 : ZMod 41)
    change (5 : ZMod 41) ≠ 0 at hp
    change (5 : ZMod 41)-1 ≠ 0 at ha
    change (5 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 41)+1)) at hr
    change IsSquare (3-(5 : ZMod 41)) at hs
    change 41=7 → (5 : ZMod 41) ≠ 3 at h7
    change 41=11 → (5 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (6 : ZMod 41)
    change (6 : ZMod 41) ≠ 0 at hp
    change (6 : ZMod 41)-1 ≠ 0 at ha
    change (6 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 41)+1)) at hr
    change IsSquare (3-(6 : ZMod 41)) at hs
    change 41=7 → (6 : ZMod 41) ≠ 3 at h7
    change 41=11 → (6 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 41)
    change (7 : ZMod 41) ≠ 0 at hp
    change (7 : ZMod 41)-1 ≠ 0 at ha
    change (7 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 41)+1)) at hr
    change IsSquare (3-(7 : ZMod 41)) at hs
    change 41=7 → (7 : ZMod 41) ≠ 3 at h7
    change 41=11 → (7 : ZMod 41) ≠ 5 at h11
    apply Or.inl
    refine ⟨7,![7,20,13,3],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (8 : ZMod 41)
    change (8 : ZMod 41) ≠ 0 at hp
    change (8 : ZMod 41)-1 ≠ 0 at ha
    change (8 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 41)+1)) at hr
    change IsSquare (3-(8 : ZMod 41)) at hs
    change 41=7 → (8 : ZMod 41) ≠ 3 at h7
    change 41=11 → (8 : ZMod 41) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![7,0,6,4],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (9 : ZMod 41)
    change (9 : ZMod 41) ≠ 0 at hp
    change (9 : ZMod 41)-1 ≠ 0 at ha
    change (9 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 41)+1)) at hr
    change IsSquare (3-(9 : ZMod 41)) at hs
    change 41=7 → (9 : ZMod 41) ≠ 3 at h7
    change 41=11 → (9 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (10 : ZMod 41)
    change (10 : ZMod 41) ≠ 0 at hp
    change (10 : ZMod 41)-1 ≠ 0 at ha
    change (10 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 41)+1)) at hr
    change IsSquare (3-(10 : ZMod 41)) at hs
    change 41=7 → (10 : ZMod 41) ≠ 3 at h7
    change 41=11 → (10 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 41)
    change (11 : ZMod 41) ≠ 0 at hp
    change (11 : ZMod 41)-1 ≠ 0 at ha
    change (11 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 41)+1)) at hr
    change IsSquare (3-(11 : ZMod 41)) at hs
    change 41=7 → (11 : ZMod 41) ≠ 3 at h7
    change 41=11 → (11 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (12 : ZMod 41)
    change (12 : ZMod 41) ≠ 0 at hp
    change (12 : ZMod 41)-1 ≠ 0 at ha
    change (12 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 41)+1)) at hr
    change IsSquare (3-(12 : ZMod 41)) at hs
    change 41=7 → (12 : ZMod 41) ≠ 3 at h7
    change 41=11 → (12 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (13 : ZMod 41)
    change (13 : ZMod 41) ≠ 0 at hp
    change (13 : ZMod 41)-1 ≠ 0 at ha
    change (13 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 41)+1)) at hr
    change IsSquare (3-(13 : ZMod 41)) at hs
    change 41=7 → (13 : ZMod 41) ≠ 3 at h7
    change 41=11 → (13 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (14 : ZMod 41)
    change (14 : ZMod 41) ≠ 0 at hp
    change (14 : ZMod 41)-1 ≠ 0 at ha
    change (14 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 41)+1)) at hr
    change IsSquare (3-(14 : ZMod 41)) at hs
    change 41=7 → (14 : ZMod 41) ≠ 3 at h7
    change 41=11 → (14 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 41)
    change (15 : ZMod 41) ≠ 0 at hp
    change (15 : ZMod 41)-1 ≠ 0 at ha
    change (15 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 41)+1)) at hr
    change IsSquare (3-(15 : ZMod 41)) at hs
    change 41=7 → (15 : ZMod 41) ≠ 3 at h7
    change 41=11 → (15 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (16 : ZMod 41)
    change (16 : ZMod 41) ≠ 0 at hp
    change (16 : ZMod 41)-1 ≠ 0 at ha
    change (16 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 41)+1)) at hr
    change IsSquare (3-(16 : ZMod 41)) at hs
    change 41=7 → (16 : ZMod 41) ≠ 3 at h7
    change 41=11 → (16 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 41)
    change (17 : ZMod 41) ≠ 0 at hp
    change (17 : ZMod 41)-1 ≠ 0 at ha
    change (17 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 41)+1)) at hr
    change IsSquare (3-(17 : ZMod 41)) at hs
    change 41=7 → (17 : ZMod 41) ≠ 3 at h7
    change 41=11 → (17 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (18 : ZMod 41)
    change (18 : ZMod 41) ≠ 0 at hp
    change (18 : ZMod 41)-1 ≠ 0 at ha
    change (18 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 41)+1)) at hr
    change IsSquare (3-(18 : ZMod 41)) at hs
    change 41=7 → (18 : ZMod 41) ≠ 3 at h7
    change 41=11 → (18 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (38 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (19 : ZMod 41)
    change (19 : ZMod 41) ≠ 0 at hp
    change (19 : ZMod 41)-1 ≠ 0 at ha
    change (19 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 41)+1)) at hr
    change IsSquare (3-(19 : ZMod 41)) at hs
    change 41=7 → (19 : ZMod 41) ≠ 3 at h7
    change 41=11 → (19 : ZMod 41) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,13,9,15],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (20 : ZMod 41)
    change (20 : ZMod 41) ≠ 0 at hp
    change (20 : ZMod 41)-1 ≠ 0 at ha
    change (20 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 41)+1)) at hr
    change IsSquare (3-(20 : ZMod 41)) at hs
    change 41=7 → (20 : ZMod 41) ≠ 3 at h7
    change 41=11 → (20 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (21 : ZMod 41)
    change (21 : ZMod 41) ≠ 0 at hp
    change (21 : ZMod 41)-1 ≠ 0 at ha
    change (21 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 41)+1)) at hr
    change IsSquare (3-(21 : ZMod 41)) at hs
    change 41=7 → (21 : ZMod 41) ≠ 3 at h7
    change 41=11 → (21 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (22 : ZMod 41)
    change (22 : ZMod 41) ≠ 0 at hp
    change (22 : ZMod 41)-1 ≠ 0 at ha
    change (22 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 41)+1)) at hr
    change IsSquare (3-(22 : ZMod 41)) at hs
    change 41=7 → (22 : ZMod 41) ≠ 3 at h7
    change 41=11 → (22 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (23 : ZMod 41)
    change (23 : ZMod 41) ≠ 0 at hp
    change (23 : ZMod 41)-1 ≠ 0 at ha
    change (23 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 41)+1)) at hr
    change IsSquare (3-(23 : ZMod 41)) at hs
    change 41=7 → (23 : ZMod 41) ≠ 3 at h7
    change 41=11 → (23 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (24 : ZMod 41)
    change (24 : ZMod 41) ≠ 0 at hp
    change (24 : ZMod 41)-1 ≠ 0 at ha
    change (24 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 41)+1)) at hr
    change IsSquare (3-(24 : ZMod 41)) at hs
    change 41=7 → (24 : ZMod 41) ≠ 3 at h7
    change 41=11 → (24 : ZMod 41) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,6,3,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (25 : ZMod 41)
    change (25 : ZMod 41) ≠ 0 at hp
    change (25 : ZMod 41)-1 ≠ 0 at ha
    change (25 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 41)+1)) at hr
    change IsSquare (3-(25 : ZMod 41)) at hs
    change 41=7 → (25 : ZMod 41) ≠ 3 at h7
    change 41=11 → (25 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (26 : ZMod 41)
    change (26 : ZMod 41) ≠ 0 at hp
    change (26 : ZMod 41)-1 ≠ 0 at ha
    change (26 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 41)+1)) at hr
    change IsSquare (3-(26 : ZMod 41)) at hs
    change 41=7 → (26 : ZMod 41) ≠ 3 at h7
    change 41=11 → (26 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (27 : ZMod 41)
    change (27 : ZMod 41) ≠ 0 at hp
    change (27 : ZMod 41)-1 ≠ 0 at ha
    change (27 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 41)+1)) at hr
    change IsSquare (3-(27 : ZMod 41)) at hs
    change 41=7 → (27 : ZMod 41) ≠ 3 at h7
    change 41=11 → (27 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (28 : ZMod 41)
    change (28 : ZMod 41) ≠ 0 at hp
    change (28 : ZMod 41)-1 ≠ 0 at ha
    change (28 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 41)+1)) at hr
    change IsSquare (3-(28 : ZMod 41)) at hs
    change 41=7 → (28 : ZMod 41) ≠ 3 at h7
    change 41=11 → (28 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (29 : ZMod 41)
    change (29 : ZMod 41) ≠ 0 at hp
    change (29 : ZMod 41)-1 ≠ 0 at ha
    change (29 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 41)+1)) at hr
    change IsSquare (3-(29 : ZMod 41)) at hs
    change 41=7 → (29 : ZMod 41) ≠ 3 at h7
    change 41=11 → (29 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (30 : ZMod 41)
    change (30 : ZMod 41) ≠ 0 at hp
    change (30 : ZMod 41)-1 ≠ 0 at ha
    change (30 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 41)+1)) at hr
    change IsSquare (3-(30 : ZMod 41)) at hs
    change 41=7 → (30 : ZMod 41) ≠ 3 at h7
    change 41=11 → (30 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (31 : ZMod 41)
    change (31 : ZMod 41) ≠ 0 at hp
    change (31 : ZMod 41)-1 ≠ 0 at ha
    change (31 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 41)+1)) at hr
    change IsSquare (3-(31 : ZMod 41)) at hs
    change 41=7 → (31 : ZMod 41) ≠ 3 at h7
    change 41=11 → (31 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (32 : ZMod 41)
    change (32 : ZMod 41) ≠ 0 at hp
    change (32 : ZMod 41)-1 ≠ 0 at ha
    change (32 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 41)+1)) at hr
    change IsSquare (3-(32 : ZMod 41)) at hs
    change 41=7 → (32 : ZMod 41) ≠ 3 at h7
    change 41=11 → (32 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (33 : ZMod 41)
    change (33 : ZMod 41) ≠ 0 at hp
    change (33 : ZMod 41)-1 ≠ 0 at ha
    change (33 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 41)+1)) at hr
    change IsSquare (3-(33 : ZMod 41)) at hs
    change 41=7 → (33 : ZMod 41) ≠ 3 at h7
    change 41=11 → (33 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (34 : ZMod 41)
    change (34 : ZMod 41) ≠ 0 at hp
    change (34 : ZMod 41)-1 ≠ 0 at ha
    change (34 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 41)+1)) at hr
    change IsSquare (3-(34 : ZMod 41)) at hs
    change 41=7 → (34 : ZMod 41) ≠ 3 at h7
    change 41=11 → (34 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (35 : ZMod 41)
    change (35 : ZMod 41) ≠ 0 at hp
    change (35 : ZMod 41)-1 ≠ 0 at ha
    change (35 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 41)+1)) at hr
    change IsSquare (3-(35 : ZMod 41)) at hs
    change 41=7 → (35 : ZMod 41) ≠ 3 at h7
    change 41=11 → (35 : ZMod 41) ≠ 5 at h11
    apply Or.inl
    refine ⟨30,![5,2,10,20],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (36 : ZMod 41)
    change (36 : ZMod 41) ≠ 0 at hp
    change (36 : ZMod 41)-1 ≠ 0 at ha
    change (36 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 41)+1)) at hr
    change IsSquare (3-(36 : ZMod 41)) at hs
    change 41=7 → (36 : ZMod 41) ≠ 3 at h7
    change 41=11 → (36 : ZMod 41) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![6,0,5,20],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (37 : ZMod 41)
    change (37 : ZMod 41) ≠ 0 at hp
    change (37 : ZMod 41)-1 ≠ 0 at ha
    change (37 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 41)+1)) at hr
    change IsSquare (3-(37 : ZMod 41)) at hs
    change 41=7 → (37 : ZMod 41) ≠ 3 at h7
    change 41=11 → (37 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (38 : ZMod 41)
    change (38 : ZMod 41) ≠ 0 at hp
    change (38 : ZMod 41)-1 ≠ 0 at ha
    change (38 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 41)+1)) at hr
    change IsSquare (3-(38 : ZMod 41)) at hs
    change 41=7 → (38 : ZMod 41) ≠ 3 at h7
    change 41=11 → (38 : ZMod 41) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 41) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (39 : ZMod 41)
    change (39 : ZMod 41) ≠ 0 at hp
    change (39 : ZMod 41)-1 ≠ 0 at ha
    change (39 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 41)+1)) at hr
    change IsSquare (3-(39 : ZMod 41)) at hs
    change 41=7 → (39 : ZMod 41) ≠ 3 at h7
    change 41=11 → (39 : ZMod 41) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![11,0,18,18],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (40 : ZMod 41)
    change (40 : ZMod 41) ≠ 0 at hp
    change (40 : ZMod 41)-1 ≠ 0 at ha
    change (40 : ZMod 41)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 41)+1)) at hr
    change IsSquare (3-(40 : ZMod 41)) at hs
    change 41=7 → (40 : ZMod 41) ≠ 3 at h7
    change 41=11 → (40 : ZMod 41) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts41

private instance prime43 : Fact (Nat.Prime 43) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts43 (p : ZMod 43) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 43=7 → p ≠ 3) (h11 : 43=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 43)
    change (0 : ZMod 43) ≠ 0 at hp
    change (0 : ZMod 43)-1 ≠ 0 at ha
    change (0 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 43)+1)) at hr
    change IsSquare (3-(0 : ZMod 43)) at hs
    change 43=7 → (0 : ZMod 43) ≠ 3 at h7
    change 43=11 → (0 : ZMod 43) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 43)
    change (1 : ZMod 43) ≠ 0 at hp
    change (1 : ZMod 43)-1 ≠ 0 at ha
    change (1 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 43)+1)) at hr
    change IsSquare (3-(1 : ZMod 43)) at hs
    change 43=7 → (1 : ZMod 43) ≠ 3 at h7
    change 43=11 → (1 : ZMod 43) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 43)
    change (2 : ZMod 43) ≠ 0 at hp
    change (2 : ZMod 43)-1 ≠ 0 at ha
    change (2 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 43)+1)) at hr
    change IsSquare (3-(2 : ZMod 43)) at hs
    change 43=7 → (2 : ZMod 43) ≠ 3 at h7
    change 43=11 → (2 : ZMod 43) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![7,2,14,7],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (3 : ZMod 43)
    change (3 : ZMod 43) ≠ 0 at hp
    change (3 : ZMod 43)-1 ≠ 0 at ha
    change (3 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 43)+1)) at hr
    change IsSquare (3-(3 : ZMod 43)) at hs
    change 43=7 → (3 : ZMod 43) ≠ 3 at h7
    change 43=11 → (3 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 43)
    change (4 : ZMod 43) ≠ 0 at hp
    change (4 : ZMod 43)-1 ≠ 0 at ha
    change (4 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 43)+1)) at hr
    change IsSquare (3-(4 : ZMod 43)) at hs
    change 43=7 → (4 : ZMod 43) ≠ 3 at h7
    change 43=11 → (4 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (42 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (5 : ZMod 43)
    change (5 : ZMod 43) ≠ 0 at hp
    change (5 : ZMod 43)-1 ≠ 0 at ha
    change (5 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 43)+1)) at hr
    change IsSquare (3-(5 : ZMod 43)) at hs
    change 43=7 → (5 : ZMod 43) ≠ 3 at h7
    change 43=11 → (5 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (6 : ZMod 43)
    change (6 : ZMod 43) ≠ 0 at hp
    change (6 : ZMod 43)-1 ≠ 0 at ha
    change (6 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 43)+1)) at hr
    change IsSquare (3-(6 : ZMod 43)) at hs
    change 43=7 → (6 : ZMod 43) ≠ 3 at h7
    change 43=11 → (6 : ZMod 43) ≠ 5 at h11
    apply Or.inl
    refine ⟨10,![19,2,5,10],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (7 : ZMod 43)
    change (7 : ZMod 43) ≠ 0 at hp
    change (7 : ZMod 43)-1 ≠ 0 at ha
    change (7 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 43)+1)) at hr
    change IsSquare (3-(7 : ZMod 43)) at hs
    change 43=7 → (7 : ZMod 43) ≠ 3 at h7
    change 43=11 → (7 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (8 : ZMod 43)
    change (8 : ZMod 43) ≠ 0 at hp
    change (8 : ZMod 43)-1 ≠ 0 at ha
    change (8 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 43)+1)) at hr
    change IsSquare (3-(8 : ZMod 43)) at hs
    change 43=7 → (8 : ZMod 43) ≠ 3 at h7
    change 43=11 → (8 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (9 : ZMod 43)
    change (9 : ZMod 43) ≠ 0 at hp
    change (9 : ZMod 43)-1 ≠ 0 at ha
    change (9 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 43)+1)) at hr
    change IsSquare (3-(9 : ZMod 43)) at hs
    change 43=7 → (9 : ZMod 43) ≠ 3 at h7
    change 43=11 → (9 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (10 : ZMod 43)
    change (10 : ZMod 43) ≠ 0 at hp
    change (10 : ZMod 43)-1 ≠ 0 at ha
    change (10 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 43)+1)) at hr
    change IsSquare (3-(10 : ZMod 43)) at hs
    change 43=7 → (10 : ZMod 43) ≠ 3 at h7
    change 43=11 → (10 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 43)
    change (11 : ZMod 43) ≠ 0 at hp
    change (11 : ZMod 43)-1 ≠ 0 at ha
    change (11 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 43)+1)) at hr
    change IsSquare (3-(11 : ZMod 43)) at hs
    change 43=7 → (11 : ZMod 43) ≠ 3 at h7
    change 43=11 → (11 : ZMod 43) ≠ 5 at h11
    apply Or.inl
    refine ⟨9,![20,17,5,4],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (12 : ZMod 43)
    change (12 : ZMod 43) ≠ 0 at hp
    change (12 : ZMod 43)-1 ≠ 0 at ha
    change (12 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 43)+1)) at hr
    change IsSquare (3-(12 : ZMod 43)) at hs
    change 43=7 → (12 : ZMod 43) ≠ 3 at h7
    change 43=11 → (12 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (13 : ZMod 43)
    change (13 : ZMod 43) ≠ 0 at hp
    change (13 : ZMod 43)-1 ≠ 0 at ha
    change (13 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 43)+1)) at hr
    change IsSquare (3-(13 : ZMod 43)) at hs
    change 43=7 → (13 : ZMod 43) ≠ 3 at h7
    change 43=11 → (13 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (14 : ZMod 43)
    change (14 : ZMod 43) ≠ 0 at hp
    change (14 : ZMod 43)-1 ≠ 0 at ha
    change (14 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 43)+1)) at hr
    change IsSquare (3-(14 : ZMod 43)) at hs
    change 43=7 → (14 : ZMod 43) ≠ 3 at h7
    change 43=11 → (14 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 43)
    change (15 : ZMod 43) ≠ 0 at hp
    change (15 : ZMod 43)-1 ≠ 0 at ha
    change (15 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 43)+1)) at hr
    change IsSquare (3-(15 : ZMod 43)) at hs
    change 43=7 → (15 : ZMod 43) ≠ 3 at h7
    change 43=11 → (15 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (32 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (16 : ZMod 43)
    change (16 : ZMod 43) ≠ 0 at hp
    change (16 : ZMod 43)-1 ≠ 0 at ha
    change (16 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 43)+1)) at hr
    change IsSquare (3-(16 : ZMod 43)) at hs
    change 43=7 → (16 : ZMod 43) ≠ 3 at h7
    change 43=11 → (16 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 43)
    change (17 : ZMod 43) ≠ 0 at hp
    change (17 : ZMod 43)-1 ≠ 0 at ha
    change (17 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 43)+1)) at hr
    change IsSquare (3-(17 : ZMod 43)) at hs
    change 43=7 → (17 : ZMod 43) ≠ 3 at h7
    change 43=11 → (17 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (18 : ZMod 43)
    change (18 : ZMod 43) ≠ 0 at hp
    change (18 : ZMod 43)-1 ≠ 0 at ha
    change (18 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 43)+1)) at hr
    change IsSquare (3-(18 : ZMod 43)) at hs
    change 43=7 → (18 : ZMod 43) ≠ 3 at h7
    change 43=11 → (18 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (19 : ZMod 43)
    change (19 : ZMod 43) ≠ 0 at hp
    change (19 : ZMod 43)-1 ≠ 0 at ha
    change (19 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 43)+1)) at hr
    change IsSquare (3-(19 : ZMod 43)) at hs
    change 43=7 → (19 : ZMod 43) ≠ 3 at h7
    change 43=11 → (19 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (20 : ZMod 43)
    change (20 : ZMod 43) ≠ 0 at hp
    change (20 : ZMod 43)-1 ≠ 0 at ha
    change (20 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 43)+1)) at hr
    change IsSquare (3-(20 : ZMod 43)) at hs
    change 43=7 → (20 : ZMod 43) ≠ 3 at h7
    change 43=11 → (20 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (42 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (21 : ZMod 43)
    change (21 : ZMod 43) ≠ 0 at hp
    change (21 : ZMod 43)-1 ≠ 0 at ha
    change (21 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 43)+1)) at hr
    change IsSquare (3-(21 : ZMod 43)) at hs
    change 43=7 → (21 : ZMod 43) ≠ 3 at h7
    change 43=11 → (21 : ZMod 43) ≠ 5 at h11
    apply Or.inl
    refine ⟨14,![6,2,12,1],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (22 : ZMod 43)
    change (22 : ZMod 43) ≠ 0 at hp
    change (22 : ZMod 43)-1 ≠ 0 at ha
    change (22 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 43)+1)) at hr
    change IsSquare (3-(22 : ZMod 43)) at hs
    change 43=7 → (22 : ZMod 43) ≠ 3 at h7
    change 43=11 → (22 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (23 : ZMod 43)
    change (23 : ZMod 43) ≠ 0 at hp
    change (23 : ZMod 43)-1 ≠ 0 at ha
    change (23 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 43)+1)) at hr
    change IsSquare (3-(23 : ZMod 43)) at hs
    change 43=7 → (23 : ZMod 43) ≠ 3 at h7
    change 43=11 → (23 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (24 : ZMod 43)
    change (24 : ZMod 43) ≠ 0 at hp
    change (24 : ZMod 43)-1 ≠ 0 at ha
    change (24 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 43)+1)) at hr
    change IsSquare (3-(24 : ZMod 43)) at hs
    change 43=7 → (24 : ZMod 43) ≠ 3 at h7
    change 43=11 → (24 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (25 : ZMod 43)
    change (25 : ZMod 43) ≠ 0 at hp
    change (25 : ZMod 43)-1 ≠ 0 at ha
    change (25 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 43)+1)) at hr
    change IsSquare (3-(25 : ZMod 43)) at hs
    change 43=7 → (25 : ZMod 43) ≠ 3 at h7
    change 43=11 → (25 : ZMod 43) ≠ 5 at h11
    apply Or.inl
    refine ⟨35,![12,16,18,7],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (26 : ZMod 43)
    change (26 : ZMod 43) ≠ 0 at hp
    change (26 : ZMod 43)-1 ≠ 0 at ha
    change (26 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 43)+1)) at hr
    change IsSquare (3-(26 : ZMod 43)) at hs
    change 43=7 → (26 : ZMod 43) ≠ 3 at h7
    change 43=11 → (26 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (27 : ZMod 43)
    change (27 : ZMod 43) ≠ 0 at hp
    change (27 : ZMod 43)-1 ≠ 0 at ha
    change (27 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 43)+1)) at hr
    change IsSquare (3-(27 : ZMod 43)) at hs
    change 43=7 → (27 : ZMod 43) ≠ 3 at h7
    change 43=11 → (27 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (28 : ZMod 43)
    change (28 : ZMod 43) ≠ 0 at hp
    change (28 : ZMod 43)-1 ≠ 0 at ha
    change (28 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 43)+1)) at hr
    change IsSquare (3-(28 : ZMod 43)) at hs
    change 43=7 → (28 : ZMod 43) ≠ 3 at h7
    change 43=11 → (28 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (29 : ZMod 43)
    change (29 : ZMod 43) ≠ 0 at hp
    change (29 : ZMod 43)-1 ≠ 0 at ha
    change (29 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 43)+1)) at hr
    change IsSquare (3-(29 : ZMod 43)) at hs
    change 43=7 → (29 : ZMod 43) ≠ 3 at h7
    change 43=11 → (29 : ZMod 43) ≠ 5 at h11
    apply Or.inl
    refine ⟨5,![4,3,4,16],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (30 : ZMod 43)
    change (30 : ZMod 43) ≠ 0 at hp
    change (30 : ZMod 43)-1 ≠ 0 at ha
    change (30 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 43)+1)) at hr
    change IsSquare (3-(30 : ZMod 43)) at hs
    change 43=7 → (30 : ZMod 43) ≠ 3 at h7
    change 43=11 → (30 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (31 : ZMod 43)
    change (31 : ZMod 43) ≠ 0 at hp
    change (31 : ZMod 43)-1 ≠ 0 at ha
    change (31 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 43)+1)) at hr
    change IsSquare (3-(31 : ZMod 43)) at hs
    change 43=7 → (31 : ZMod 43) ≠ 3 at h7
    change 43=11 → (31 : ZMod 43) ≠ 5 at h11
    apply Or.inl
    refine ⟨10,![3,14,4,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (32 : ZMod 43)
    change (32 : ZMod 43) ≠ 0 at hp
    change (32 : ZMod 43)-1 ≠ 0 at ha
    change (32 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 43)+1)) at hr
    change IsSquare (3-(32 : ZMod 43)) at hs
    change 43=7 → (32 : ZMod 43) ≠ 3 at h7
    change 43=11 → (32 : ZMod 43) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![15,9,7,13],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (33 : ZMod 43)
    change (33 : ZMod 43) ≠ 0 at hp
    change (33 : ZMod 43)-1 ≠ 0 at ha
    change (33 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 43)+1)) at hr
    change IsSquare (3-(33 : ZMod 43)) at hs
    change 43=7 → (33 : ZMod 43) ≠ 3 at h7
    change 43=11 → (33 : ZMod 43) ≠ 5 at h11
    apply Or.inl
    refine ⟨12,![3,4,14,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (34 : ZMod 43)
    change (34 : ZMod 43) ≠ 0 at hp
    change (34 : ZMod 43)-1 ≠ 0 at ha
    change (34 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 43)+1)) at hr
    change IsSquare (3-(34 : ZMod 43)) at hs
    change 43=7 → (34 : ZMod 43) ≠ 3 at h7
    change 43=11 → (34 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (35 : ZMod 43)
    change (35 : ZMod 43) ≠ 0 at hp
    change (35 : ZMod 43)-1 ≠ 0 at ha
    change (35 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 43)+1)) at hr
    change IsSquare (3-(35 : ZMod 43)) at hs
    change 43=7 → (35 : ZMod 43) ≠ 3 at h7
    change 43=11 → (35 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (36 : ZMod 43)
    change (36 : ZMod 43) ≠ 0 at hp
    change (36 : ZMod 43)-1 ≠ 0 at ha
    change (36 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 43)+1)) at hr
    change IsSquare (3-(36 : ZMod 43)) at hs
    change 43=7 → (36 : ZMod 43) ≠ 3 at h7
    change 43=11 → (36 : ZMod 43) ≠ 5 at h11
    apply Or.inl
    refine ⟨23,![21,11,20,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (37 : ZMod 43)
    change (37 : ZMod 43) ≠ 0 at hp
    change (37 : ZMod 43)-1 ≠ 0 at ha
    change (37 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 43)+1)) at hr
    change IsSquare (3-(37 : ZMod 43)) at hs
    change 43=7 → (37 : ZMod 43) ≠ 3 at h7
    change 43=11 → (37 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (38 : ZMod 43)
    change (38 : ZMod 43) ≠ 0 at hp
    change (38 : ZMod 43)-1 ≠ 0 at ha
    change (38 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 43)+1)) at hr
    change IsSquare (3-(38 : ZMod 43)) at hs
    change 43=7 → (38 : ZMod 43) ≠ 3 at h7
    change 43=11 → (38 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (39 : ZMod 43)
    change (39 : ZMod 43) ≠ 0 at hp
    change (39 : ZMod 43)-1 ≠ 0 at ha
    change (39 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 43)+1)) at hr
    change IsSquare (3-(39 : ZMod 43)) at hs
    change 43=7 → (39 : ZMod 43) ≠ 3 at h7
    change 43=11 → (39 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (37 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (40 : ZMod 43)
    change (40 : ZMod 43) ≠ 0 at hp
    change (40 : ZMod 43)-1 ≠ 0 at ha
    change (40 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 43)+1)) at hr
    change IsSquare (3-(40 : ZMod 43)) at hs
    change 43=7 → (40 : ZMod 43) ≠ 3 at h7
    change 43=11 → (40 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (41 : ZMod 43)
    change (41 : ZMod 43) ≠ 0 at hp
    change (41 : ZMod 43)-1 ≠ 0 at ha
    change (41 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 43)+1)) at hr
    change IsSquare (3-(41 : ZMod 43)) at hs
    change 43=7 → (41 : ZMod 43) ≠ 3 at h7
    change 43=11 → (41 : ZMod 43) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 43) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (42 : ZMod 43)
    change (42 : ZMod 43) ≠ 0 at hp
    change (42 : ZMod 43)-1 ≠ 0 at ha
    change (42 : ZMod 43)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 43)+1)) at hr
    change IsSquare (3-(42 : ZMod 43)) at hs
    change 43=7 → (42 : ZMod 43) ≠ 3 at h7
    change 43=11 → (42 : ZMod 43) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts43

private instance prime47 : Fact (Nat.Prime 47) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts47 (p : ZMod 47) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 47=7 → p ≠ 3) (h11 : 47=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 47)
    change (0 : ZMod 47) ≠ 0 at hp
    change (0 : ZMod 47)-1 ≠ 0 at ha
    change (0 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 47)+1)) at hr
    change IsSquare (3-(0 : ZMod 47)) at hs
    change 47=7 → (0 : ZMod 47) ≠ 3 at h7
    change 47=11 → (0 : ZMod 47) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 47)
    change (1 : ZMod 47) ≠ 0 at hp
    change (1 : ZMod 47)-1 ≠ 0 at ha
    change (1 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 47)+1)) at hr
    change IsSquare (3-(1 : ZMod 47)) at hs
    change 47=7 → (1 : ZMod 47) ≠ 3 at h7
    change 47=11 → (1 : ZMod 47) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 47)
    change (2 : ZMod 47) ≠ 0 at hp
    change (2 : ZMod 47)-1 ≠ 0 at ha
    change (2 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 47)+1)) at hr
    change IsSquare (3-(2 : ZMod 47)) at hs
    change 47=7 → (2 : ZMod 47) ≠ 3 at h7
    change 47=11 → (2 : ZMod 47) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![7,0,23,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (3 : ZMod 47)
    change (3 : ZMod 47) ≠ 0 at hp
    change (3 : ZMod 47)-1 ≠ 0 at ha
    change (3 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 47)+1)) at hr
    change IsSquare (3-(3 : ZMod 47)) at hs
    change 47=7 → (3 : ZMod 47) ≠ 3 at h7
    change 47=11 → (3 : ZMod 47) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![12,0,4,10],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (4 : ZMod 47)
    change (4 : ZMod 47) ≠ 0 at hp
    change (4 : ZMod 47)-1 ≠ 0 at ha
    change (4 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 47)+1)) at hr
    change IsSquare (3-(4 : ZMod 47)) at hs
    change 47=7 → (4 : ZMod 47) ≠ 3 at h7
    change 47=11 → (4 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (5 : ZMod 47)
    change (5 : ZMod 47) ≠ 0 at hp
    change (5 : ZMod 47)-1 ≠ 0 at ha
    change (5 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 47)+1)) at hr
    change IsSquare (3-(5 : ZMod 47)) at hs
    change 47=7 → (5 : ZMod 47) ≠ 3 at h7
    change 47=11 → (5 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (45 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (6 : ZMod 47)
    change (6 : ZMod 47) ≠ 0 at hp
    change (6 : ZMod 47)-1 ≠ 0 at ha
    change (6 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 47)+1)) at hr
    change IsSquare (3-(6 : ZMod 47)) at hs
    change 47=7 → (6 : ZMod 47) ≠ 3 at h7
    change 47=11 → (6 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (44 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (7 : ZMod 47)
    change (7 : ZMod 47) ≠ 0 at hp
    change (7 : ZMod 47)-1 ≠ 0 at ha
    change (7 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 47)+1)) at hr
    change IsSquare (3-(7 : ZMod 47)) at hs
    change 47=7 → (7 : ZMod 47) ≠ 3 at h7
    change 47=11 → (7 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (8 : ZMod 47)
    change (8 : ZMod 47) ≠ 0 at hp
    change (8 : ZMod 47)-1 ≠ 0 at ha
    change (8 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 47)+1)) at hr
    change IsSquare (3-(8 : ZMod 47)) at hs
    change 47=7 → (8 : ZMod 47) ≠ 3 at h7
    change 47=11 → (8 : ZMod 47) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![14,0,6,4],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (9 : ZMod 47)
    change (9 : ZMod 47) ≠ 0 at hp
    change (9 : ZMod 47)-1 ≠ 0 at ha
    change (9 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 47)+1)) at hr
    change IsSquare (3-(9 : ZMod 47)) at hs
    change 47=7 → (9 : ZMod 47) ≠ 3 at h7
    change 47=11 → (9 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (10 : ZMod 47)
    change (10 : ZMod 47) ≠ 0 at hp
    change (10 : ZMod 47)-1 ≠ 0 at ha
    change (10 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 47)+1)) at hr
    change IsSquare (3-(10 : ZMod 47)) at hs
    change 47=7 → (10 : ZMod 47) ≠ 3 at h7
    change 47=11 → (10 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 47)
    change (11 : ZMod 47) ≠ 0 at hp
    change (11 : ZMod 47)-1 ≠ 0 at ha
    change (11 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 47)+1)) at hr
    change IsSquare (3-(11 : ZMod 47)) at hs
    change 47=7 → (11 : ZMod 47) ≠ 3 at h7
    change 47=11 → (11 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (12 : ZMod 47)
    change (12 : ZMod 47) ≠ 0 at hp
    change (12 : ZMod 47)-1 ≠ 0 at ha
    change (12 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 47)+1)) at hr
    change IsSquare (3-(12 : ZMod 47)) at hs
    change 47=7 → (12 : ZMod 47) ≠ 3 at h7
    change 47=11 → (12 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (13 : ZMod 47)
    change (13 : ZMod 47) ≠ 0 at hp
    change (13 : ZMod 47)-1 ≠ 0 at ha
    change (13 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 47)+1)) at hr
    change IsSquare (3-(13 : ZMod 47)) at hs
    change 47=7 → (13 : ZMod 47) ≠ 3 at h7
    change 47=11 → (13 : ZMod 47) ≠ 5 at h11
    apply Or.inl
    refine ⟨5,![21,7,11,11],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (14 : ZMod 47)
    change (14 : ZMod 47) ≠ 0 at hp
    change (14 : ZMod 47)-1 ≠ 0 at ha
    change (14 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 47)+1)) at hr
    change IsSquare (3-(14 : ZMod 47)) at hs
    change 47=7 → (14 : ZMod 47) ≠ 3 at h7
    change 47=11 → (14 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 47)
    change (15 : ZMod 47) ≠ 0 at hp
    change (15 : ZMod 47)-1 ≠ 0 at ha
    change (15 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 47)+1)) at hr
    change IsSquare (3-(15 : ZMod 47)) at hs
    change 47=7 → (15 : ZMod 47) ≠ 3 at h7
    change 47=11 → (15 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (16 : ZMod 47)
    change (16 : ZMod 47) ≠ 0 at hp
    change (16 : ZMod 47)-1 ≠ 0 at ha
    change (16 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 47)+1)) at hr
    change IsSquare (3-(16 : ZMod 47)) at hs
    change 47=7 → (16 : ZMod 47) ≠ 3 at h7
    change 47=11 → (16 : ZMod 47) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,8,9,8],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (17 : ZMod 47)
    change (17 : ZMod 47) ≠ 0 at hp
    change (17 : ZMod 47)-1 ≠ 0 at ha
    change (17 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 47)+1)) at hr
    change IsSquare (3-(17 : ZMod 47)) at hs
    change 47=7 → (17 : ZMod 47) ≠ 3 at h7
    change 47=11 → (17 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (18 : ZMod 47)
    change (18 : ZMod 47) ≠ 0 at hp
    change (18 : ZMod 47)-1 ≠ 0 at ha
    change (18 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 47)+1)) at hr
    change IsSquare (3-(18 : ZMod 47)) at hs
    change 47=7 → (18 : ZMod 47) ≠ 3 at h7
    change 47=11 → (18 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (38 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (19 : ZMod 47)
    change (19 : ZMod 47) ≠ 0 at hp
    change (19 : ZMod 47)-1 ≠ 0 at ha
    change (19 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 47)+1)) at hr
    change IsSquare (3-(19 : ZMod 47)) at hs
    change 47=7 → (19 : ZMod 47) ≠ 3 at h7
    change 47=11 → (19 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (40 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (20 : ZMod 47)
    change (20 : ZMod 47) ≠ 0 at hp
    change (20 : ZMod 47)-1 ≠ 0 at ha
    change (20 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 47)+1)) at hr
    change IsSquare (3-(20 : ZMod 47)) at hs
    change 47=7 → (20 : ZMod 47) ≠ 3 at h7
    change 47=11 → (20 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (21 : ZMod 47)
    change (21 : ZMod 47) ≠ 0 at hp
    change (21 : ZMod 47)-1 ≠ 0 at ha
    change (21 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 47)+1)) at hr
    change IsSquare (3-(21 : ZMod 47)) at hs
    change 47=7 → (21 : ZMod 47) ≠ 3 at h7
    change 47=11 → (21 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (44 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (22 : ZMod 47)
    change (22 : ZMod 47) ≠ 0 at hp
    change (22 : ZMod 47)-1 ≠ 0 at ha
    change (22 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 47)+1)) at hr
    change IsSquare (3-(22 : ZMod 47)) at hs
    change 47=7 → (22 : ZMod 47) ≠ 3 at h7
    change 47=11 → (22 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (46 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (23 : ZMod 47)
    change (23 : ZMod 47) ≠ 0 at hp
    change (23 : ZMod 47)-1 ≠ 0 at ha
    change (23 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 47)+1)) at hr
    change IsSquare (3-(23 : ZMod 47)) at hs
    change 47=7 → (23 : ZMod 47) ≠ 3 at h7
    change 47=11 → (23 : ZMod 47) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,12,1,20],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (24 : ZMod 47)
    change (24 : ZMod 47) ≠ 0 at hp
    change (24 : ZMod 47)-1 ≠ 0 at ha
    change (24 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 47)+1)) at hr
    change IsSquare (3-(24 : ZMod 47)) at hs
    change 47=7 → (24 : ZMod 47) ≠ 3 at h7
    change 47=11 → (24 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (25 : ZMod 47)
    change (25 : ZMod 47) ≠ 0 at hp
    change (25 : ZMod 47)-1 ≠ 0 at ha
    change (25 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 47)+1)) at hr
    change IsSquare (3-(25 : ZMod 47)) at hs
    change 47=7 → (25 : ZMod 47) ≠ 3 at h7
    change 47=11 → (25 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (26 : ZMod 47)
    change (26 : ZMod 47) ≠ 0 at hp
    change (26 : ZMod 47)-1 ≠ 0 at ha
    change (26 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 47)+1)) at hr
    change IsSquare (3-(26 : ZMod 47)) at hs
    change 47=7 → (26 : ZMod 47) ≠ 3 at h7
    change 47=11 → (26 : ZMod 47) ≠ 5 at h11
    apply Or.inl
    refine ⟨33,![23,7,12,10],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (27 : ZMod 47)
    change (27 : ZMod 47) ≠ 0 at hp
    change (27 : ZMod 47)-1 ≠ 0 at ha
    change (27 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 47)+1)) at hr
    change IsSquare (3-(27 : ZMod 47)) at hs
    change 47=7 → (27 : ZMod 47) ≠ 3 at h7
    change 47=11 → (27 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (28 : ZMod 47)
    change (28 : ZMod 47) ≠ 0 at hp
    change (28 : ZMod 47)-1 ≠ 0 at ha
    change (28 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 47)+1)) at hr
    change IsSquare (3-(28 : ZMod 47)) at hs
    change 47=7 → (28 : ZMod 47) ≠ 3 at h7
    change 47=11 → (28 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (29 : ZMod 47)
    change (29 : ZMod 47) ≠ 0 at hp
    change (29 : ZMod 47)-1 ≠ 0 at ha
    change (29 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 47)+1)) at hr
    change IsSquare (3-(29 : ZMod 47)) at hs
    change 47=7 → (29 : ZMod 47) ≠ 3 at h7
    change 47=11 → (29 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (30 : ZMod 47)
    change (30 : ZMod 47) ≠ 0 at hp
    change (30 : ZMod 47)-1 ≠ 0 at ha
    change (30 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 47)+1)) at hr
    change IsSquare (3-(30 : ZMod 47)) at hs
    change 47=7 → (30 : ZMod 47) ≠ 3 at h7
    change 47=11 → (30 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (31 : ZMod 47)
    change (31 : ZMod 47) ≠ 0 at hp
    change (31 : ZMod 47)-1 ≠ 0 at ha
    change (31 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 47)+1)) at hr
    change IsSquare (3-(31 : ZMod 47)) at hs
    change 47=7 → (31 : ZMod 47) ≠ 3 at h7
    change 47=11 → (31 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (32 : ZMod 47)
    change (32 : ZMod 47) ≠ 0 at hp
    change (32 : ZMod 47)-1 ≠ 0 at ha
    change (32 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 47)+1)) at hr
    change IsSquare (3-(32 : ZMod 47)) at hs
    change 47=7 → (32 : ZMod 47) ≠ 3 at h7
    change 47=11 → (32 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (33 : ZMod 47)
    change (33 : ZMod 47) ≠ 0 at hp
    change (33 : ZMod 47)-1 ≠ 0 at ha
    change (33 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 47)+1)) at hr
    change IsSquare (3-(33 : ZMod 47)) at hs
    change 47=7 → (33 : ZMod 47) ≠ 3 at h7
    change 47=11 → (33 : ZMod 47) ≠ 5 at h11
    apply Or.inl
    refine ⟨5,![20,16,19,10],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (34 : ZMod 47)
    change (34 : ZMod 47) ≠ 0 at hp
    change (34 : ZMod 47)-1 ≠ 0 at ha
    change (34 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 47)+1)) at hr
    change IsSquare (3-(34 : ZMod 47)) at hs
    change 47=7 → (34 : ZMod 47) ≠ 3 at h7
    change 47=11 → (34 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (35 : ZMod 47)
    change (35 : ZMod 47) ≠ 0 at hp
    change (35 : ZMod 47)-1 ≠ 0 at ha
    change (35 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 47)+1)) at hr
    change IsSquare (3-(35 : ZMod 47)) at hs
    change 47=7 → (35 : ZMod 47) ≠ 3 at h7
    change 47=11 → (35 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (36 : ZMod 47)
    change (36 : ZMod 47) ≠ 0 at hp
    change (36 : ZMod 47)-1 ≠ 0 at ha
    change (36 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 47)+1)) at hr
    change IsSquare (3-(36 : ZMod 47)) at hs
    change 47=7 → (36 : ZMod 47) ≠ 3 at h7
    change 47=11 → (36 : ZMod 47) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,20,11,15],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (37 : ZMod 47)
    change (37 : ZMod 47) ≠ 0 at hp
    change (37 : ZMod 47)-1 ≠ 0 at ha
    change (37 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 47)+1)) at hr
    change IsSquare (3-(37 : ZMod 47)) at hs
    change 47=7 → (37 : ZMod 47) ≠ 3 at h7
    change 47=11 → (37 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (38 : ZMod 47)
    change (38 : ZMod 47) ≠ 0 at hp
    change (38 : ZMod 47)-1 ≠ 0 at ha
    change (38 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 47)+1)) at hr
    change IsSquare (3-(38 : ZMod 47)) at hs
    change 47=7 → (38 : ZMod 47) ≠ 3 at h7
    change 47=11 → (38 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (39 : ZMod 47)
    change (39 : ZMod 47) ≠ 0 at hp
    change (39 : ZMod 47)-1 ≠ 0 at ha
    change (39 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 47)+1)) at hr
    change IsSquare (3-(39 : ZMod 47)) at hs
    change 47=7 → (39 : ZMod 47) ≠ 3 at h7
    change 47=11 → (39 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (40 : ZMod 47)
    change (40 : ZMod 47) ≠ 0 at hp
    change (40 : ZMod 47)-1 ≠ 0 at ha
    change (40 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 47)+1)) at hr
    change IsSquare (3-(40 : ZMod 47)) at hs
    change 47=7 → (40 : ZMod 47) ≠ 3 at h7
    change 47=11 → (40 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (41 : ZMod 47)
    change (41 : ZMod 47) ≠ 0 at hp
    change (41 : ZMod 47)-1 ≠ 0 at ha
    change (41 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 47)+1)) at hr
    change IsSquare (3-(41 : ZMod 47)) at hs
    change 47=7 → (41 : ZMod 47) ≠ 3 at h7
    change 47=11 → (41 : ZMod 47) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,22,15,18],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (42 : ZMod 47)
    change (42 : ZMod 47) ≠ 0 at hp
    change (42 : ZMod 47)-1 ≠ 0 at ha
    change (42 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 47)+1)) at hr
    change IsSquare (3-(42 : ZMod 47)) at hs
    change 47=7 → (42 : ZMod 47) ≠ 3 at h7
    change 47=11 → (42 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (43 : ZMod 47)
    change (43 : ZMod 47) ≠ 0 at hp
    change (43 : ZMod 47)-1 ≠ 0 at ha
    change (43 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((43 : ZMod 47)+1)) at hr
    change IsSquare (3-(43 : ZMod 47)) at hs
    change 47=7 → (43 : ZMod 47) ≠ 3 at h7
    change 47=11 → (43 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (41 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (44 : ZMod 47)
    change (44 : ZMod 47) ≠ 0 at hp
    change (44 : ZMod 47)-1 ≠ 0 at ha
    change (44 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((44 : ZMod 47)+1)) at hr
    change IsSquare (3-(44 : ZMod 47)) at hs
    change 47=7 → (44 : ZMod 47) ≠ 3 at h7
    change 47=11 → (44 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (45 : ZMod 47)
    change (45 : ZMod 47) ≠ 0 at hp
    change (45 : ZMod 47)-1 ≠ 0 at ha
    change (45 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((45 : ZMod 47)+1)) at hr
    change IsSquare (3-(45 : ZMod 47)) at hs
    change 47=7 → (45 : ZMod 47) ≠ 3 at h7
    change 47=11 → (45 : ZMod 47) ≠ 5 at h11
    have hn : ¬IsSquare (45 : ZMod 47) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (46 : ZMod 47)
    change (46 : ZMod 47) ≠ 0 at hp
    change (46 : ZMod 47)-1 ≠ 0 at ha
    change (46 : ZMod 47)+1 ≠ 0 at hb
    change IsSquare (2*((46 : ZMod 47)+1)) at hr
    change IsSquare (3-(46 : ZMod 47)) at hs
    change 47=7 → (46 : ZMod 47) ≠ 3 at h7
    change 47=11 → (46 : ZMod 47) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts47

private instance prime53 : Fact (Nat.Prime 53) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts53 (p : ZMod 53) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 53=7 → p ≠ 3) (h11 : 53=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 53)
    change (0 : ZMod 53) ≠ 0 at hp
    change (0 : ZMod 53)-1 ≠ 0 at ha
    change (0 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 53)+1)) at hr
    change IsSquare (3-(0 : ZMod 53)) at hs
    change 53=7 → (0 : ZMod 53) ≠ 3 at h7
    change 53=11 → (0 : ZMod 53) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 53)
    change (1 : ZMod 53) ≠ 0 at hp
    change (1 : ZMod 53)-1 ≠ 0 at ha
    change (1 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 53)+1)) at hr
    change IsSquare (3-(1 : ZMod 53)) at hs
    change 53=7 → (1 : ZMod 53) ≠ 3 at h7
    change 53=11 → (1 : ZMod 53) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 53)
    change (2 : ZMod 53) ≠ 0 at hp
    change (2 : ZMod 53)-1 ≠ 0 at ha
    change (2 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 53)+1)) at hr
    change IsSquare (3-(2 : ZMod 53)) at hs
    change 53=7 → (2 : ZMod 53) ≠ 3 at h7
    change 53=11 → (2 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![18,2,17,18],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (3 : ZMod 53)
    change (3 : ZMod 53) ≠ 0 at hp
    change (3 : ZMod 53)-1 ≠ 0 at ha
    change (3 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 53)+1)) at hr
    change IsSquare (3-(3 : ZMod 53)) at hs
    change 53=7 → (3 : ZMod 53) ≠ 3 at h7
    change 53=11 → (3 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 53)
    change (4 : ZMod 53) ≠ 0 at hp
    change (4 : ZMod 53)-1 ≠ 0 at ha
    change (4 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 53)+1)) at hr
    change IsSquare (3-(4 : ZMod 53)) at hs
    change 53=7 → (4 : ZMod 53) ≠ 3 at h7
    change 53=11 → (4 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨16,![8,14,8,0],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (5 : ZMod 53)
    change (5 : ZMod 53) ≠ 0 at hp
    change (5 : ZMod 53)-1 ≠ 0 at ha
    change (5 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 53)+1)) at hr
    change IsSquare (3-(5 : ZMod 53)) at hs
    change 53=7 → (5 : ZMod 53) ≠ 3 at h7
    change 53=11 → (5 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (6 : ZMod 53)
    change (6 : ZMod 53) ≠ 0 at hp
    change (6 : ZMod 53)-1 ≠ 0 at ha
    change (6 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 53)+1)) at hr
    change IsSquare (3-(6 : ZMod 53)) at hs
    change 53=7 → (6 : ZMod 53) ≠ 3 at h7
    change 53=11 → (6 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 53)
    change (7 : ZMod 53) ≠ 0 at hp
    change (7 : ZMod 53)-1 ≠ 0 at ha
    change (7 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 53)+1)) at hr
    change IsSquare (3-(7 : ZMod 53)) at hs
    change 53=7 → (7 : ZMod 53) ≠ 3 at h7
    change 53=11 → (7 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![25,22,18,16],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (8 : ZMod 53)
    change (8 : ZMod 53) ≠ 0 at hp
    change (8 : ZMod 53)-1 ≠ 0 at ha
    change (8 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 53)+1)) at hr
    change IsSquare (3-(8 : ZMod 53)) at hs
    change 53=7 → (8 : ZMod 53) ≠ 3 at h7
    change 53=11 → (8 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (9 : ZMod 53)
    change (9 : ZMod 53) ≠ 0 at hp
    change (9 : ZMod 53)-1 ≠ 0 at ha
    change (9 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 53)+1)) at hr
    change IsSquare (3-(9 : ZMod 53)) at hs
    change 53=7 → (9 : ZMod 53) ≠ 3 at h7
    change 53=11 → (9 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (10 : ZMod 53)
    change (10 : ZMod 53) ≠ 0 at hp
    change (10 : ZMod 53)-1 ≠ 0 at ha
    change (10 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 53)+1)) at hr
    change IsSquare (3-(10 : ZMod 53)) at hs
    change 53=7 → (10 : ZMod 53) ≠ 3 at h7
    change 53=11 → (10 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 53)
    change (11 : ZMod 53) ≠ 0 at hp
    change (11 : ZMod 53)-1 ≠ 0 at ha
    change (11 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 53)+1)) at hr
    change IsSquare (3-(11 : ZMod 53)) at hs
    change 53=7 → (11 : ZMod 53) ≠ 3 at h7
    change 53=11 → (11 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (45 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (12 : ZMod 53)
    change (12 : ZMod 53) ≠ 0 at hp
    change (12 : ZMod 53)-1 ≠ 0 at ha
    change (12 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 53)+1)) at hr
    change IsSquare (3-(12 : ZMod 53)) at hs
    change 53=7 → (12 : ZMod 53) ≠ 3 at h7
    change 53=11 → (12 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (13 : ZMod 53)
    change (13 : ZMod 53) ≠ 0 at hp
    change (13 : ZMod 53)-1 ≠ 0 at ha
    change (13 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 53)+1)) at hr
    change IsSquare (3-(13 : ZMod 53)) at hs
    change 53=7 → (13 : ZMod 53) ≠ 3 at h7
    change 53=11 → (13 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨10,![17,2,19,9],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (14 : ZMod 53)
    change (14 : ZMod 53) ≠ 0 at hp
    change (14 : ZMod 53)-1 ≠ 0 at ha
    change (14 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 53)+1)) at hr
    change IsSquare (3-(14 : ZMod 53)) at hs
    change 53=7 → (14 : ZMod 53) ≠ 3 at h7
    change 53=11 → (14 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 53)
    change (15 : ZMod 53) ≠ 0 at hp
    change (15 : ZMod 53)-1 ≠ 0 at ha
    change (15 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 53)+1)) at hr
    change IsSquare (3-(15 : ZMod 53)) at hs
    change 53=7 → (15 : ZMod 53) ≠ 3 at h7
    change 53=11 → (15 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (32 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (16 : ZMod 53)
    change (16 : ZMod 53) ≠ 0 at hp
    change (16 : ZMod 53)-1 ≠ 0 at ha
    change (16 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 53)+1)) at hr
    change IsSquare (3-(16 : ZMod 53)) at hs
    change 53=7 → (16 : ZMod 53) ≠ 3 at h7
    change 53=11 → (16 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 53)
    change (17 : ZMod 53) ≠ 0 at hp
    change (17 : ZMod 53)-1 ≠ 0 at ha
    change (17 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 53)+1)) at hr
    change IsSquare (3-(17 : ZMod 53)) at hs
    change 53=7 → (17 : ZMod 53) ≠ 3 at h7
    change 53=11 → (17 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (18 : ZMod 53)
    change (18 : ZMod 53) ≠ 0 at hp
    change (18 : ZMod 53)-1 ≠ 0 at ha
    change (18 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 53)+1)) at hr
    change IsSquare (3-(18 : ZMod 53)) at hs
    change 53=7 → (18 : ZMod 53) ≠ 3 at h7
    change 53=11 → (18 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![1,11,24,21],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (19 : ZMod 53)
    change (19 : ZMod 53) ≠ 0 at hp
    change (19 : ZMod 53)-1 ≠ 0 at ha
    change (19 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 53)+1)) at hr
    change IsSquare (3-(19 : ZMod 53)) at hs
    change 53=7 → (19 : ZMod 53) ≠ 3 at h7
    change 53=11 → (19 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨5,![25,12,9,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (20 : ZMod 53)
    change (20 : ZMod 53) ≠ 0 at hp
    change (20 : ZMod 53)-1 ≠ 0 at ha
    change (20 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 53)+1)) at hr
    change IsSquare (3-(20 : ZMod 53)) at hs
    change 53=7 → (20 : ZMod 53) ≠ 3 at h7
    change 53=11 → (20 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨5,![10,24,26,13],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (21 : ZMod 53)
    change (21 : ZMod 53) ≠ 0 at hp
    change (21 : ZMod 53)-1 ≠ 0 at ha
    change (21 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 53)+1)) at hr
    change IsSquare (3-(21 : ZMod 53)) at hs
    change 53=7 → (21 : ZMod 53) ≠ 3 at h7
    change 53=11 → (21 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (22 : ZMod 53)
    change (22 : ZMod 53) ≠ 0 at hp
    change (22 : ZMod 53)-1 ≠ 0 at ha
    change (22 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 53)+1)) at hr
    change IsSquare (3-(22 : ZMod 53)) at hs
    change 53=7 → (22 : ZMod 53) ≠ 3 at h7
    change 53=11 → (22 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (23 : ZMod 53)
    change (23 : ZMod 53) ≠ 0 at hp
    change (23 : ZMod 53)-1 ≠ 0 at ha
    change (23 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 53)+1)) at hr
    change IsSquare (3-(23 : ZMod 53)) at hs
    change 53=7 → (23 : ZMod 53) ≠ 3 at h7
    change 53=11 → (23 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (48 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (24 : ZMod 53)
    change (24 : ZMod 53) ≠ 0 at hp
    change (24 : ZMod 53)-1 ≠ 0 at ha
    change (24 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 53)+1)) at hr
    change IsSquare (3-(24 : ZMod 53)) at hs
    change 53=7 → (24 : ZMod 53) ≠ 3 at h7
    change 53=11 → (24 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (50 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (25 : ZMod 53)
    change (25 : ZMod 53) ≠ 0 at hp
    change (25 : ZMod 53)-1 ≠ 0 at ha
    change (25 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 53)+1)) at hr
    change IsSquare (3-(25 : ZMod 53)) at hs
    change 53=7 → (25 : ZMod 53) ≠ 3 at h7
    change 53=11 → (25 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (26 : ZMod 53)
    change (26 : ZMod 53) ≠ 0 at hp
    change (26 : ZMod 53)-1 ≠ 0 at ha
    change (26 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 53)+1)) at hr
    change IsSquare (3-(26 : ZMod 53)) at hs
    change 53=7 → (26 : ZMod 53) ≠ 3 at h7
    change 53=11 → (26 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (27 : ZMod 53)
    change (27 : ZMod 53) ≠ 0 at hp
    change (27 : ZMod 53)-1 ≠ 0 at ha
    change (27 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 53)+1)) at hr
    change IsSquare (3-(27 : ZMod 53)) at hs
    change 53=7 → (27 : ZMod 53) ≠ 3 at h7
    change 53=11 → (27 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (28 : ZMod 53)
    change (28 : ZMod 53) ≠ 0 at hp
    change (28 : ZMod 53)-1 ≠ 0 at ha
    change (28 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 53)+1)) at hr
    change IsSquare (3-(28 : ZMod 53)) at hs
    change 53=7 → (28 : ZMod 53) ≠ 3 at h7
    change 53=11 → (28 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (29 : ZMod 53)
    change (29 : ZMod 53) ≠ 0 at hp
    change (29 : ZMod 53)-1 ≠ 0 at ha
    change (29 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 53)+1)) at hr
    change IsSquare (3-(29 : ZMod 53)) at hs
    change 53=7 → (29 : ZMod 53) ≠ 3 at h7
    change 53=11 → (29 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (30 : ZMod 53)
    change (30 : ZMod 53) ≠ 0 at hp
    change (30 : ZMod 53)-1 ≠ 0 at ha
    change (30 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 53)+1)) at hr
    change IsSquare (3-(30 : ZMod 53)) at hs
    change 53=7 → (30 : ZMod 53) ≠ 3 at h7
    change 53=11 → (30 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (31 : ZMod 53)
    change (31 : ZMod 53) ≠ 0 at hp
    change (31 : ZMod 53)-1 ≠ 0 at ha
    change (31 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 53)+1)) at hr
    change IsSquare (3-(31 : ZMod 53)) at hs
    change 53=7 → (31 : ZMod 53) ≠ 3 at h7
    change 53=11 → (31 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨8,![6,7,24,22],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (32 : ZMod 53)
    change (32 : ZMod 53) ≠ 0 at hp
    change (32 : ZMod 53)-1 ≠ 0 at ha
    change (32 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 53)+1)) at hr
    change IsSquare (3-(32 : ZMod 53)) at hs
    change 53=7 → (32 : ZMod 53) ≠ 3 at h7
    change 53=11 → (32 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨5,![1,6,5,20],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (33 : ZMod 53)
    change (33 : ZMod 53) ≠ 0 at hp
    change (33 : ZMod 53)-1 ≠ 0 at ha
    change (33 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 53)+1)) at hr
    change IsSquare (3-(33 : ZMod 53)) at hs
    change 53=7 → (33 : ZMod 53) ≠ 3 at h7
    change 53=11 → (33 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (34 : ZMod 53)
    change (34 : ZMod 53) ≠ 0 at hp
    change (34 : ZMod 53)-1 ≠ 0 at ha
    change (34 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 53)+1)) at hr
    change IsSquare (3-(34 : ZMod 53)) at hs
    change 53=7 → (34 : ZMod 53) ≠ 3 at h7
    change 53=11 → (34 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (35 : ZMod 53)
    change (35 : ZMod 53) ≠ 0 at hp
    change (35 : ZMod 53)-1 ≠ 0 at ha
    change (35 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 53)+1)) at hr
    change IsSquare (3-(35 : ZMod 53)) at hs
    change 53=7 → (35 : ZMod 53) ≠ 3 at h7
    change 53=11 → (35 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (36 : ZMod 53)
    change (36 : ZMod 53) ≠ 0 at hp
    change (36 : ZMod 53)-1 ≠ 0 at ha
    change (36 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 53)+1)) at hr
    change IsSquare (3-(36 : ZMod 53)) at hs
    change 53=7 → (36 : ZMod 53) ≠ 3 at h7
    change 53=11 → (36 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (37 : ZMod 53)
    change (37 : ZMod 53) ≠ 0 at hp
    change (37 : ZMod 53)-1 ≠ 0 at ha
    change (37 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 53)+1)) at hr
    change IsSquare (3-(37 : ZMod 53)) at hs
    change 53=7 → (37 : ZMod 53) ≠ 3 at h7
    change 53=11 → (37 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (38 : ZMod 53)
    change (38 : ZMod 53) ≠ 0 at hp
    change (38 : ZMod 53)-1 ≠ 0 at ha
    change (38 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 53)+1)) at hr
    change IsSquare (3-(38 : ZMod 53)) at hs
    change 53=7 → (38 : ZMod 53) ≠ 3 at h7
    change 53=11 → (38 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (39 : ZMod 53)
    change (39 : ZMod 53) ≠ 0 at hp
    change (39 : ZMod 53)-1 ≠ 0 at ha
    change (39 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 53)+1)) at hr
    change IsSquare (3-(39 : ZMod 53)) at hs
    change 53=7 → (39 : ZMod 53) ≠ 3 at h7
    change 53=11 → (39 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (40 : ZMod 53)
    change (40 : ZMod 53) ≠ 0 at hp
    change (40 : ZMod 53)-1 ≠ 0 at ha
    change (40 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 53)+1)) at hr
    change IsSquare (3-(40 : ZMod 53)) at hs
    change 53=7 → (40 : ZMod 53) ≠ 3 at h7
    change 53=11 → (40 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨10,![20,15,1,22],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (41 : ZMod 53)
    change (41 : ZMod 53) ≠ 0 at hp
    change (41 : ZMod 53)-1 ≠ 0 at ha
    change (41 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 53)+1)) at hr
    change IsSquare (3-(41 : ZMod 53)) at hs
    change 53=7 → (41 : ZMod 53) ≠ 3 at h7
    change 53=11 → (41 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (42 : ZMod 53)
    change (42 : ZMod 53) ≠ 0 at hp
    change (42 : ZMod 53)-1 ≠ 0 at ha
    change (42 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 53)+1)) at hr
    change IsSquare (3-(42 : ZMod 53)) at hs
    change 53=7 → (42 : ZMod 53) ≠ 3 at h7
    change 53=11 → (42 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (43 : ZMod 53)
    change (43 : ZMod 53) ≠ 0 at hp
    change (43 : ZMod 53)-1 ≠ 0 at ha
    change (43 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((43 : ZMod 53)+1)) at hr
    change IsSquare (3-(43 : ZMod 53)) at hs
    change 53=7 → (43 : ZMod 53) ≠ 3 at h7
    change 53=11 → (43 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (44 : ZMod 53)
    change (44 : ZMod 53) ≠ 0 at hp
    change (44 : ZMod 53)-1 ≠ 0 at ha
    change (44 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((44 : ZMod 53)+1)) at hr
    change IsSquare (3-(44 : ZMod 53)) at hs
    change 53=7 → (44 : ZMod 53) ≠ 3 at h7
    change 53=11 → (44 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (45 : ZMod 53)
    change (45 : ZMod 53) ≠ 0 at hp
    change (45 : ZMod 53)-1 ≠ 0 at ha
    change (45 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((45 : ZMod 53)+1)) at hr
    change IsSquare (3-(45 : ZMod 53)) at hs
    change 53=7 → (45 : ZMod 53) ≠ 3 at h7
    change 53=11 → (45 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (46 : ZMod 53)
    change (46 : ZMod 53) ≠ 0 at hp
    change (46 : ZMod 53)-1 ≠ 0 at ha
    change (46 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((46 : ZMod 53)+1)) at hr
    change IsSquare (3-(46 : ZMod 53)) at hs
    change 53=7 → (46 : ZMod 53) ≠ 3 at h7
    change 53=11 → (46 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (41 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (47 : ZMod 53)
    change (47 : ZMod 53) ≠ 0 at hp
    change (47 : ZMod 53)-1 ≠ 0 at ha
    change (47 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((47 : ZMod 53)+1)) at hr
    change IsSquare (3-(47 : ZMod 53)) at hs
    change 53=7 → (47 : ZMod 53) ≠ 3 at h7
    change 53=11 → (47 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![21,6,6,18],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (48 : ZMod 53)
    change (48 : ZMod 53) ≠ 0 at hp
    change (48 : ZMod 53)-1 ≠ 0 at ha
    change (48 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((48 : ZMod 53)+1)) at hr
    change IsSquare (3-(48 : ZMod 53)) at hs
    change 53=7 → (48 : ZMod 53) ≠ 3 at h7
    change 53=11 → (48 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (45 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (49 : ZMod 53)
    change (49 : ZMod 53) ≠ 0 at hp
    change (49 : ZMod 53)-1 ≠ 0 at ha
    change (49 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((49 : ZMod 53)+1)) at hr
    change IsSquare (3-(49 : ZMod 53)) at hs
    change 53=7 → (49 : ZMod 53) ≠ 3 at h7
    change 53=11 → (49 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨10,![15,4,26,0],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (50 : ZMod 53)
    change (50 : ZMod 53) ≠ 0 at hp
    change (50 : ZMod 53)-1 ≠ 0 at ha
    change (50 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((50 : ZMod 53)+1)) at hr
    change IsSquare (3-(50 : ZMod 53)) at hs
    change 53=7 → (50 : ZMod 53) ≠ 3 at h7
    change 53=11 → (50 : ZMod 53) ≠ 5 at h11
    apply Or.inl
    refine ⟨27,![5,2,10,7],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (51 : ZMod 53)
    change (51 : ZMod 53) ≠ 0 at hp
    change (51 : ZMod 53)-1 ≠ 0 at ha
    change (51 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((51 : ZMod 53)+1)) at hr
    change IsSquare (3-(51 : ZMod 53)) at hs
    change 53=7 → (51 : ZMod 53) ≠ 3 at h7
    change 53=11 → (51 : ZMod 53) ≠ 5 at h11
    have hn : ¬IsSquare (51 : ZMod 53) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (52 : ZMod 53)
    change (52 : ZMod 53) ≠ 0 at hp
    change (52 : ZMod 53)-1 ≠ 0 at ha
    change (52 : ZMod 53)+1 ≠ 0 at hb
    change IsSquare (2*((52 : ZMod 53)+1)) at hr
    change IsSquare (3-(52 : ZMod 53)) at hs
    change 53=7 → (52 : ZMod 53) ≠ 3 at h7
    change 53=11 → (52 : ZMod 53) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts53

private instance prime59 : Fact (Nat.Prime 59) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts59 (p : ZMod 59) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 59=7 → p ≠ 3) (h11 : 59=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 59)
    change (0 : ZMod 59) ≠ 0 at hp
    change (0 : ZMod 59)-1 ≠ 0 at ha
    change (0 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 59)+1)) at hr
    change IsSquare (3-(0 : ZMod 59)) at hs
    change 59=7 → (0 : ZMod 59) ≠ 3 at h7
    change 59=11 → (0 : ZMod 59) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 59)
    change (1 : ZMod 59) ≠ 0 at hp
    change (1 : ZMod 59)-1 ≠ 0 at ha
    change (1 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 59)+1)) at hr
    change IsSquare (3-(1 : ZMod 59)) at hs
    change 59=7 → (1 : ZMod 59) ≠ 3 at h7
    change 59=11 → (1 : ZMod 59) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 59)
    change (2 : ZMod 59) ≠ 0 at hp
    change (2 : ZMod 59)-1 ≠ 0 at ha
    change (2 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 59)+1)) at hr
    change IsSquare (3-(2 : ZMod 59)) at hs
    change 59=7 → (2 : ZMod 59) ≠ 3 at h7
    change 59=11 → (2 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 59)
    change (3 : ZMod 59) ≠ 0 at hp
    change (3 : ZMod 59)-1 ≠ 0 at ha
    change (3 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 59)+1)) at hr
    change IsSquare (3-(3 : ZMod 59)) at hs
    change 59=7 → (3 : ZMod 59) ≠ 3 at h7
    change 59=11 → (3 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 59)
    change (4 : ZMod 59) ≠ 0 at hp
    change (4 : ZMod 59)-1 ≠ 0 at ha
    change (4 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 59)+1)) at hr
    change IsSquare (3-(4 : ZMod 59)) at hs
    change 59=7 → (4 : ZMod 59) ≠ 3 at h7
    change 59=11 → (4 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (5 : ZMod 59)
    change (5 : ZMod 59) ≠ 0 at hp
    change (5 : ZMod 59)-1 ≠ 0 at ha
    change (5 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 59)+1)) at hr
    change IsSquare (3-(5 : ZMod 59)) at hs
    change 59=7 → (5 : ZMod 59) ≠ 3 at h7
    change 59=11 → (5 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![4,17,29,19],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (6 : ZMod 59)
    change (6 : ZMod 59) ≠ 0 at hp
    change (6 : ZMod 59)-1 ≠ 0 at ha
    change (6 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 59)+1)) at hr
    change IsSquare (3-(6 : ZMod 59)) at hs
    change 59=7 → (6 : ZMod 59) ≠ 3 at h7
    change 59=11 → (6 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 59)
    change (7 : ZMod 59) ≠ 0 at hp
    change (7 : ZMod 59)-1 ≠ 0 at ha
    change (7 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 59)+1)) at hr
    change IsSquare (3-(7 : ZMod 59)) at hs
    change 59=7 → (7 : ZMod 59) ≠ 3 at h7
    change 59=11 → (7 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (55 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (8 : ZMod 59)
    change (8 : ZMod 59) ≠ 0 at hp
    change (8 : ZMod 59)-1 ≠ 0 at ha
    change (8 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 59)+1)) at hr
    change IsSquare (3-(8 : ZMod 59)) at hs
    change 59=7 → (8 : ZMod 59) ≠ 3 at h7
    change 59=11 → (8 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (9 : ZMod 59)
    change (9 : ZMod 59) ≠ 0 at hp
    change (9 : ZMod 59)-1 ≠ 0 at ha
    change (9 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 59)+1)) at hr
    change IsSquare (3-(9 : ZMod 59)) at hs
    change 59=7 → (9 : ZMod 59) ≠ 3 at h7
    change 59=11 → (9 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨16,![12,2,24,16],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (10 : ZMod 59)
    change (10 : ZMod 59) ≠ 0 at hp
    change (10 : ZMod 59)-1 ≠ 0 at ha
    change (10 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 59)+1)) at hr
    change IsSquare (3-(10 : ZMod 59)) at hs
    change 59=7 → (10 : ZMod 59) ≠ 3 at h7
    change 59=11 → (10 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (52 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (11 : ZMod 59)
    change (11 : ZMod 59) ≠ 0 at hp
    change (11 : ZMod 59)-1 ≠ 0 at ha
    change (11 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 59)+1)) at hr
    change IsSquare (3-(11 : ZMod 59)) at hs
    change 59=7 → (11 : ZMod 59) ≠ 3 at h7
    change 59=11 → (11 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (12 : ZMod 59)
    change (12 : ZMod 59) ≠ 0 at hp
    change (12 : ZMod 59)-1 ≠ 0 at ha
    change (12 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 59)+1)) at hr
    change IsSquare (3-(12 : ZMod 59)) at hs
    change 59=7 → (12 : ZMod 59) ≠ 3 at h7
    change 59=11 → (12 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (50 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (13 : ZMod 59)
    change (13 : ZMod 59) ≠ 0 at hp
    change (13 : ZMod 59)-1 ≠ 0 at ha
    change (13 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 59)+1)) at hr
    change IsSquare (3-(13 : ZMod 59)) at hs
    change 59=7 → (13 : ZMod 59) ≠ 3 at h7
    change 59=11 → (13 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨11,![5,2,10,21],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (14 : ZMod 59)
    change (14 : ZMod 59) ≠ 0 at hp
    change (14 : ZMod 59)-1 ≠ 0 at ha
    change (14 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 59)+1)) at hr
    change IsSquare (3-(14 : ZMod 59)) at hs
    change 59=7 → (14 : ZMod 59) ≠ 3 at h7
    change 59=11 → (14 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 59)
    change (15 : ZMod 59) ≠ 0 at hp
    change (15 : ZMod 59)-1 ≠ 0 at ha
    change (15 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 59)+1)) at hr
    change IsSquare (3-(15 : ZMod 59)) at hs
    change 59=7 → (15 : ZMod 59) ≠ 3 at h7
    change 59=11 → (15 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (32 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (16 : ZMod 59)
    change (16 : ZMod 59) ≠ 0 at hp
    change (16 : ZMod 59)-1 ≠ 0 at ha
    change (16 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 59)+1)) at hr
    change IsSquare (3-(16 : ZMod 59)) at hs
    change 59=7 → (16 : ZMod 59) ≠ 3 at h7
    change 59=11 → (16 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 59)
    change (17 : ZMod 59) ≠ 0 at hp
    change (17 : ZMod 59)-1 ≠ 0 at ha
    change (17 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 59)+1)) at hr
    change IsSquare (3-(17 : ZMod 59)) at hs
    change 59=7 → (17 : ZMod 59) ≠ 3 at h7
    change 59=11 → (17 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![13,8,12,19],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (18 : ZMod 59)
    change (18 : ZMod 59) ≠ 0 at hp
    change (18 : ZMod 59)-1 ≠ 0 at ha
    change (18 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 59)+1)) at hr
    change IsSquare (3-(18 : ZMod 59)) at hs
    change 59=7 → (18 : ZMod 59) ≠ 3 at h7
    change 59=11 → (18 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (38 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (19 : ZMod 59)
    change (19 : ZMod 59) ≠ 0 at hp
    change (19 : ZMod 59)-1 ≠ 0 at ha
    change (19 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 59)+1)) at hr
    change IsSquare (3-(19 : ZMod 59)) at hs
    change 59=7 → (19 : ZMod 59) ≠ 3 at h7
    change 59=11 → (19 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (40 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (20 : ZMod 59)
    change (20 : ZMod 59) ≠ 0 at hp
    change (20 : ZMod 59)-1 ≠ 0 at ha
    change (20 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 59)+1)) at hr
    change IsSquare (3-(20 : ZMod 59)) at hs
    change 59=7 → (20 : ZMod 59) ≠ 3 at h7
    change 59=11 → (20 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (42 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (21 : ZMod 59)
    change (21 : ZMod 59) ≠ 0 at hp
    change (21 : ZMod 59)-1 ≠ 0 at ha
    change (21 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 59)+1)) at hr
    change IsSquare (3-(21 : ZMod 59)) at hs
    change 59=7 → (21 : ZMod 59) ≠ 3 at h7
    change 59=11 → (21 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (44 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (22 : ZMod 59)
    change (22 : ZMod 59) ≠ 0 at hp
    change (22 : ZMod 59)-1 ≠ 0 at ha
    change (22 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 59)+1)) at hr
    change IsSquare (3-(22 : ZMod 59)) at hs
    change 59=7 → (22 : ZMod 59) ≠ 3 at h7
    change 59=11 → (22 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (40 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (23 : ZMod 59)
    change (23 : ZMod 59) ≠ 0 at hp
    change (23 : ZMod 59)-1 ≠ 0 at ha
    change (23 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 59)+1)) at hr
    change IsSquare (3-(23 : ZMod 59)) at hs
    change 59=7 → (23 : ZMod 59) ≠ 3 at h7
    change 59=11 → (23 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (24 : ZMod 59)
    change (24 : ZMod 59) ≠ 0 at hp
    change (24 : ZMod 59)-1 ≠ 0 at ha
    change (24 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 59)+1)) at hr
    change IsSquare (3-(24 : ZMod 59)) at hs
    change 59=7 → (24 : ZMod 59) ≠ 3 at h7
    change 59=11 → (24 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (50 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (25 : ZMod 59)
    change (25 : ZMod 59) ≠ 0 at hp
    change (25 : ZMod 59)-1 ≠ 0 at ha
    change (25 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 59)+1)) at hr
    change IsSquare (3-(25 : ZMod 59)) at hs
    change 59=7 → (25 : ZMod 59) ≠ 3 at h7
    change 59=11 → (25 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (52 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (26 : ZMod 59)
    change (26 : ZMod 59) ≠ 0 at hp
    change (26 : ZMod 59)-1 ≠ 0 at ha
    change (26 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 59)+1)) at hr
    change IsSquare (3-(26 : ZMod 59)) at hs
    change 59=7 → (26 : ZMod 59) ≠ 3 at h7
    change 59=11 → (26 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (54 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (27 : ZMod 59)
    change (27 : ZMod 59) ≠ 0 at hp
    change (27 : ZMod 59)-1 ≠ 0 at ha
    change (27 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 59)+1)) at hr
    change IsSquare (3-(27 : ZMod 59)) at hs
    change 59=7 → (27 : ZMod 59) ≠ 3 at h7
    change 59=11 → (27 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (56 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (28 : ZMod 59)
    change (28 : ZMod 59) ≠ 0 at hp
    change (28 : ZMod 59)-1 ≠ 0 at ha
    change (28 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 59)+1)) at hr
    change IsSquare (3-(28 : ZMod 59)) at hs
    change 59=7 → (28 : ZMod 59) ≠ 3 at h7
    change 59=11 → (28 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (58 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (29 : ZMod 59)
    change (29 : ZMod 59) ≠ 0 at hp
    change (29 : ZMod 59)-1 ≠ 0 at ha
    change (29 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 59)+1)) at hr
    change IsSquare (3-(29 : ZMod 59)) at hs
    change 59=7 → (29 : ZMod 59) ≠ 3 at h7
    change 59=11 → (29 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (30 : ZMod 59)
    change (30 : ZMod 59) ≠ 0 at hp
    change (30 : ZMod 59)-1 ≠ 0 at ha
    change (30 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 59)+1)) at hr
    change IsSquare (3-(30 : ZMod 59)) at hs
    change 59=7 → (30 : ZMod 59) ≠ 3 at h7
    change 59=11 → (30 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (32 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (31 : ZMod 59)
    change (31 : ZMod 59) ≠ 0 at hp
    change (31 : ZMod 59)-1 ≠ 0 at ha
    change (31 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 59)+1)) at hr
    change IsSquare (3-(31 : ZMod 59)) at hs
    change 59=7 → (31 : ZMod 59) ≠ 3 at h7
    change 59=11 → (31 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (32 : ZMod 59)
    change (32 : ZMod 59) ≠ 0 at hp
    change (32 : ZMod 59)-1 ≠ 0 at ha
    change (32 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 59)+1)) at hr
    change IsSquare (3-(32 : ZMod 59)) at hs
    change 59=7 → (32 : ZMod 59) ≠ 3 at h7
    change 59=11 → (32 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (33 : ZMod 59)
    change (33 : ZMod 59) ≠ 0 at hp
    change (33 : ZMod 59)-1 ≠ 0 at ha
    change (33 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 59)+1)) at hr
    change IsSquare (3-(33 : ZMod 59)) at hs
    change 59=7 → (33 : ZMod 59) ≠ 3 at h7
    change 59=11 → (33 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![27,5,2,7],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (34 : ZMod 59)
    change (34 : ZMod 59) ≠ 0 at hp
    change (34 : ZMod 59)-1 ≠ 0 at ha
    change (34 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 59)+1)) at hr
    change IsSquare (3-(34 : ZMod 59)) at hs
    change 59=7 → (34 : ZMod 59) ≠ 3 at h7
    change 59=11 → (34 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (35 : ZMod 59)
    change (35 : ZMod 59) ≠ 0 at hp
    change (35 : ZMod 59)-1 ≠ 0 at ha
    change (35 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 59)+1)) at hr
    change IsSquare (3-(35 : ZMod 59)) at hs
    change 59=7 → (35 : ZMod 59) ≠ 3 at h7
    change 59=11 → (35 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (36 : ZMod 59)
    change (36 : ZMod 59) ≠ 0 at hp
    change (36 : ZMod 59)-1 ≠ 0 at ha
    change (36 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 59)+1)) at hr
    change IsSquare (3-(36 : ZMod 59)) at hs
    change 59=7 → (36 : ZMod 59) ≠ 3 at h7
    change 59=11 → (36 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨19,![25,27,8,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (37 : ZMod 59)
    change (37 : ZMod 59) ≠ 0 at hp
    change (37 : ZMod 59)-1 ≠ 0 at ha
    change (37 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 59)+1)) at hr
    change IsSquare (3-(37 : ZMod 59)) at hs
    change 59=7 → (37 : ZMod 59) ≠ 3 at h7
    change 59=11 → (37 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨11,![17,22,26,27],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (38 : ZMod 59)
    change (38 : ZMod 59) ≠ 0 at hp
    change (38 : ZMod 59)-1 ≠ 0 at ha
    change (38 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 59)+1)) at hr
    change IsSquare (3-(38 : ZMod 59)) at hs
    change 59=7 → (38 : ZMod 59) ≠ 3 at h7
    change 59=11 → (38 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (39 : ZMod 59)
    change (39 : ZMod 59) ≠ 0 at hp
    change (39 : ZMod 59)-1 ≠ 0 at ha
    change (39 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 59)+1)) at hr
    change IsSquare (3-(39 : ZMod 59)) at hs
    change 59=7 → (39 : ZMod 59) ≠ 3 at h7
    change 59=11 → (39 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (40 : ZMod 59)
    change (40 : ZMod 59) ≠ 0 at hp
    change (40 : ZMod 59)-1 ≠ 0 at ha
    change (40 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 59)+1)) at hr
    change IsSquare (3-(40 : ZMod 59)) at hs
    change 59=7 → (40 : ZMod 59) ≠ 3 at h7
    change 59=11 → (40 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (41 : ZMod 59)
    change (41 : ZMod 59) ≠ 0 at hp
    change (41 : ZMod 59)-1 ≠ 0 at ha
    change (41 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 59)+1)) at hr
    change IsSquare (3-(41 : ZMod 59)) at hs
    change 59=7 → (41 : ZMod 59) ≠ 3 at h7
    change 59=11 → (41 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨4,![20,2,19,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (42 : ZMod 59)
    change (42 : ZMod 59) ≠ 0 at hp
    change (42 : ZMod 59)-1 ≠ 0 at ha
    change (42 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 59)+1)) at hr
    change IsSquare (3-(42 : ZMod 59)) at hs
    change 59=7 → (42 : ZMod 59) ≠ 3 at h7
    change 59=11 → (42 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨11,![7,17,18,9],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (43 : ZMod 59)
    change (43 : ZMod 59) ≠ 0 at hp
    change (43 : ZMod 59)-1 ≠ 0 at ha
    change (43 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((43 : ZMod 59)+1)) at hr
    change IsSquare (3-(43 : ZMod 59)) at hs
    change 59=7 → (43 : ZMod 59) ≠ 3 at h7
    change 59=11 → (43 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![9,19,12,1],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (44 : ZMod 59)
    change (44 : ZMod 59) ≠ 0 at hp
    change (44 : ZMod 59)-1 ≠ 0 at ha
    change (44 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((44 : ZMod 59)+1)) at hr
    change IsSquare (3-(44 : ZMod 59)) at hs
    change 59=7 → (44 : ZMod 59) ≠ 3 at h7
    change 59=11 → (44 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (45 : ZMod 59)
    change (45 : ZMod 59) ≠ 0 at hp
    change (45 : ZMod 59)-1 ≠ 0 at ha
    change (45 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((45 : ZMod 59)+1)) at hr
    change IsSquare (3-(45 : ZMod 59)) at hs
    change 59=7 → (45 : ZMod 59) ≠ 3 at h7
    change 59=11 → (45 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (46 : ZMod 59)
    change (46 : ZMod 59) ≠ 0 at hp
    change (46 : ZMod 59)-1 ≠ 0 at ha
    change (46 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((46 : ZMod 59)+1)) at hr
    change IsSquare (3-(46 : ZMod 59)) at hs
    change 59=7 → (46 : ZMod 59) ≠ 3 at h7
    change 59=11 → (46 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![16,11,9,8],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (47 : ZMod 59)
    change (47 : ZMod 59) ≠ 0 at hp
    change (47 : ZMod 59)-1 ≠ 0 at ha
    change (47 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((47 : ZMod 59)+1)) at hr
    change IsSquare (3-(47 : ZMod 59)) at hs
    change 59=7 → (47 : ZMod 59) ≠ 3 at h7
    change 59=11 → (47 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (37 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (48 : ZMod 59)
    change (48 : ZMod 59) ≠ 0 at hp
    change (48 : ZMod 59)-1 ≠ 0 at ha
    change (48 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((48 : ZMod 59)+1)) at hr
    change IsSquare (3-(48 : ZMod 59)) at hs
    change 59=7 → (48 : ZMod 59) ≠ 3 at h7
    change 59=11 → (48 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (49 : ZMod 59)
    change (49 : ZMod 59) ≠ 0 at hp
    change (49 : ZMod 59)-1 ≠ 0 at ha
    change (49 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((49 : ZMod 59)+1)) at hr
    change IsSquare (3-(49 : ZMod 59)) at hs
    change 59=7 → (49 : ZMod 59) ≠ 3 at h7
    change 59=11 → (49 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (50 : ZMod 59)
    change (50 : ZMod 59) ≠ 0 at hp
    change (50 : ZMod 59)-1 ≠ 0 at ha
    change (50 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((50 : ZMod 59)+1)) at hr
    change IsSquare (3-(50 : ZMod 59)) at hs
    change 59=7 → (50 : ZMod 59) ≠ 3 at h7
    change 59=11 → (50 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (51 : ZMod 59)
    change (51 : ZMod 59) ≠ 0 at hp
    change (51 : ZMod 59)-1 ≠ 0 at ha
    change (51 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((51 : ZMod 59)+1)) at hr
    change IsSquare (3-(51 : ZMod 59)) at hs
    change 59=7 → (51 : ZMod 59) ≠ 3 at h7
    change 59=11 → (51 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (52 : ZMod 59)
    change (52 : ZMod 59) ≠ 0 at hp
    change (52 : ZMod 59)-1 ≠ 0 at ha
    change (52 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((52 : ZMod 59)+1)) at hr
    change IsSquare (3-(52 : ZMod 59)) at hs
    change 59=7 → (52 : ZMod 59) ≠ 3 at h7
    change 59=11 → (52 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (47 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (53 : ZMod 59)
    change (53 : ZMod 59) ≠ 0 at hp
    change (53 : ZMod 59)-1 ≠ 0 at ha
    change (53 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((53 : ZMod 59)+1)) at hr
    change IsSquare (3-(53 : ZMod 59)) at hs
    change 59=7 → (53 : ZMod 59) ≠ 3 at h7
    change 59=11 → (53 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨4,![25,28,3,12],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (54 : ZMod 59)
    change (54 : ZMod 59) ≠ 0 at hp
    change (54 : ZMod 59)-1 ≠ 0 at ha
    change (54 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((54 : ZMod 59)+1)) at hr
    change IsSquare (3-(54 : ZMod 59)) at hs
    change 59=7 → (54 : ZMod 59) ≠ 3 at h7
    change 59=11 → (54 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (55 : ZMod 59)
    change (55 : ZMod 59) ≠ 0 at hp
    change (55 : ZMod 59)-1 ≠ 0 at ha
    change (55 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((55 : ZMod 59)+1)) at hr
    change IsSquare (3-(55 : ZMod 59)) at hs
    change 59=7 → (55 : ZMod 59) ≠ 3 at h7
    change 59=11 → (55 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨2,![13,7,10,20],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (56 : ZMod 59)
    change (56 : ZMod 59) ≠ 0 at hp
    change (56 : ZMod 59)-1 ≠ 0 at ha
    change (56 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((56 : ZMod 59)+1)) at hr
    change IsSquare (3-(56 : ZMod 59)) at hs
    change 59=7 → (56 : ZMod 59) ≠ 3 at h7
    change 59=11 → (56 : ZMod 59) ≠ 5 at h11
    have hn : ¬IsSquare (55 : ZMod 59) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (57 : ZMod 59)
    change (57 : ZMod 59) ≠ 0 at hp
    change (57 : ZMod 59)-1 ≠ 0 at ha
    change (57 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((57 : ZMod 59)+1)) at hr
    change IsSquare (3-(57 : ZMod 59)) at hs
    change 59=7 → (57 : ZMod 59) ≠ 3 at h7
    change 59=11 → (57 : ZMod 59) ≠ 5 at h11
    apply Or.inl
    refine ⟨4,![13,10,7,20],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (58 : ZMod 59)
    change (58 : ZMod 59) ≠ 0 at hp
    change (58 : ZMod 59)-1 ≠ 0 at ha
    change (58 : ZMod 59)+1 ≠ 0 at hb
    change IsSquare (2*((58 : ZMod 59)+1)) at hr
    change IsSquare (3-(58 : ZMod 59)) at hs
    change 59=7 → (58 : ZMod 59) ≠ 3 at h7
    change 59=11 → (58 : ZMod 59) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts59

private instance prime61 : Fact (Nat.Prime 61) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts61 (p : ZMod 61) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 61=7 → p ≠ 3) (h11 : 61=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 61)
    change (0 : ZMod 61) ≠ 0 at hp
    change (0 : ZMod 61)-1 ≠ 0 at ha
    change (0 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 61)+1)) at hr
    change IsSquare (3-(0 : ZMod 61)) at hs
    change 61=7 → (0 : ZMod 61) ≠ 3 at h7
    change 61=11 → (0 : ZMod 61) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 61)
    change (1 : ZMod 61) ≠ 0 at hp
    change (1 : ZMod 61)-1 ≠ 0 at ha
    change (1 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 61)+1)) at hr
    change IsSquare (3-(1 : ZMod 61)) at hs
    change 61=7 → (1 : ZMod 61) ≠ 3 at h7
    change 61=11 → (1 : ZMod 61) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 61)
    change (2 : ZMod 61) ≠ 0 at hp
    change (2 : ZMod 61)-1 ≠ 0 at ha
    change (2 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 61)+1)) at hr
    change IsSquare (3-(2 : ZMod 61)) at hs
    change 61=7 → (2 : ZMod 61) ≠ 3 at h7
    change 61=11 → (2 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 61)
    change (3 : ZMod 61) ≠ 0 at hp
    change (3 : ZMod 61)-1 ≠ 0 at ha
    change (3 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 61)+1)) at hr
    change IsSquare (3-(3 : ZMod 61)) at hs
    change 61=7 → (3 : ZMod 61) ≠ 3 at h7
    change 61=11 → (3 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 61)
    change (4 : ZMod 61) ≠ 0 at hp
    change (4 : ZMod 61)-1 ≠ 0 at ha
    change (4 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 61)+1)) at hr
    change IsSquare (3-(4 : ZMod 61)) at hs
    change 61=7 → (4 : ZMod 61) ≠ 3 at h7
    change 61=11 → (4 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (5 : ZMod 61)
    change (5 : ZMod 61) ≠ 0 at hp
    change (5 : ZMod 61)-1 ≠ 0 at ha
    change (5 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 61)+1)) at hr
    change IsSquare (3-(5 : ZMod 61)) at hs
    change 61=7 → (5 : ZMod 61) ≠ 3 at h7
    change 61=11 → (5 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (59 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (6 : ZMod 61)
    change (6 : ZMod 61) ≠ 0 at hp
    change (6 : ZMod 61)-1 ≠ 0 at ha
    change (6 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 61)+1)) at hr
    change IsSquare (3-(6 : ZMod 61)) at hs
    change 61=7 → (6 : ZMod 61) ≠ 3 at h7
    change 61=11 → (6 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨8,![29,3,2,13],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (7 : ZMod 61)
    change (7 : ZMod 61) ≠ 0 at hp
    change (7 : ZMod 61)-1 ≠ 0 at ha
    change (7 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 61)+1)) at hr
    change IsSquare (3-(7 : ZMod 61)) at hs
    change 61=7 → (7 : ZMod 61) ≠ 3 at h7
    change 61=11 → (7 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨2,![21,16,29,9],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (8 : ZMod 61)
    change (8 : ZMod 61) ≠ 0 at hp
    change (8 : ZMod 61)-1 ≠ 0 at ha
    change (8 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 61)+1)) at hr
    change IsSquare (3-(8 : ZMod 61)) at hs
    change 61=7 → (8 : ZMod 61) ≠ 3 at h7
    change 61=11 → (8 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (9 : ZMod 61)
    change (9 : ZMod 61) ≠ 0 at hp
    change (9 : ZMod 61)-1 ≠ 0 at ha
    change (9 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 61)+1)) at hr
    change IsSquare (3-(9 : ZMod 61)) at hs
    change 61=7 → (9 : ZMod 61) ≠ 3 at h7
    change 61=11 → (9 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (55 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (10 : ZMod 61)
    change (10 : ZMod 61) ≠ 0 at hp
    change (10 : ZMod 61)-1 ≠ 0 at ha
    change (10 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 61)+1)) at hr
    change IsSquare (3-(10 : ZMod 61)) at hs
    change 61=7 → (10 : ZMod 61) ≠ 3 at h7
    change 61=11 → (10 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (54 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (11 : ZMod 61)
    change (11 : ZMod 61) ≠ 0 at hp
    change (11 : ZMod 61)-1 ≠ 0 at ha
    change (11 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 61)+1)) at hr
    change IsSquare (3-(11 : ZMod 61)) at hs
    change 61=7 → (11 : ZMod 61) ≠ 3 at h7
    change 61=11 → (11 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (12 : ZMod 61)
    change (12 : ZMod 61) ≠ 0 at hp
    change (12 : ZMod 61)-1 ≠ 0 at ha
    change (12 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 61)+1)) at hr
    change IsSquare (3-(12 : ZMod 61)) at hs
    change 61=7 → (12 : ZMod 61) ≠ 3 at h7
    change 61=11 → (12 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (13 : ZMod 61)
    change (13 : ZMod 61) ≠ 0 at hp
    change (13 : ZMod 61)-1 ≠ 0 at ha
    change (13 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 61)+1)) at hr
    change IsSquare (3-(13 : ZMod 61)) at hs
    change 61=7 → (13 : ZMod 61) ≠ 3 at h7
    change 61=11 → (13 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (14 : ZMod 61)
    change (14 : ZMod 61) ≠ 0 at hp
    change (14 : ZMod 61)-1 ≠ 0 at ha
    change (14 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 61)+1)) at hr
    change IsSquare (3-(14 : ZMod 61)) at hs
    change 61=7 → (14 : ZMod 61) ≠ 3 at h7
    change 61=11 → (14 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 61)
    change (15 : ZMod 61) ≠ 0 at hp
    change (15 : ZMod 61)-1 ≠ 0 at ha
    change (15 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 61)+1)) at hr
    change IsSquare (3-(15 : ZMod 61)) at hs
    change 61=7 → (15 : ZMod 61) ≠ 3 at h7
    change 61=11 → (15 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (32 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (16 : ZMod 61)
    change (16 : ZMod 61) ≠ 0 at hp
    change (16 : ZMod 61)-1 ≠ 0 at ha
    change (16 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 61)+1)) at hr
    change IsSquare (3-(16 : ZMod 61)) at hs
    change 61=7 → (16 : ZMod 61) ≠ 3 at h7
    change 61=11 → (16 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![29,11,21,1],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (17 : ZMod 61)
    change (17 : ZMod 61) ≠ 0 at hp
    change (17 : ZMod 61)-1 ≠ 0 at ha
    change (17 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 61)+1)) at hr
    change IsSquare (3-(17 : ZMod 61)) at hs
    change 61=7 → (17 : ZMod 61) ≠ 3 at h7
    change 61=11 → (17 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨18,![1,19,14,1],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (18 : ZMod 61)
    change (18 : ZMod 61) ≠ 0 at hp
    change (18 : ZMod 61)-1 ≠ 0 at ha
    change (18 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 61)+1)) at hr
    change IsSquare (3-(18 : ZMod 61)) at hs
    change 61=7 → (18 : ZMod 61) ≠ 3 at h7
    change 61=11 → (18 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (38 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (19 : ZMod 61)
    change (19 : ZMod 61) ≠ 0 at hp
    change (19 : ZMod 61)-1 ≠ 0 at ha
    change (19 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 61)+1)) at hr
    change IsSquare (3-(19 : ZMod 61)) at hs
    change 61=7 → (19 : ZMod 61) ≠ 3 at h7
    change 61=11 → (19 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (40 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (20 : ZMod 61)
    change (20 : ZMod 61) ≠ 0 at hp
    change (20 : ZMod 61)-1 ≠ 0 at ha
    change (20 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 61)+1)) at hr
    change IsSquare (3-(20 : ZMod 61)) at hs
    change 61=7 → (20 : ZMod 61) ≠ 3 at h7
    change 61=11 → (20 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (44 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (21 : ZMod 61)
    change (21 : ZMod 61) ≠ 0 at hp
    change (21 : ZMod 61)-1 ≠ 0 at ha
    change (21 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 61)+1)) at hr
    change IsSquare (3-(21 : ZMod 61)) at hs
    change 61=7 → (21 : ZMod 61) ≠ 3 at h7
    change 61=11 → (21 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (44 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (22 : ZMod 61)
    change (22 : ZMod 61) ≠ 0 at hp
    change (22 : ZMod 61)-1 ≠ 0 at ha
    change (22 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 61)+1)) at hr
    change IsSquare (3-(22 : ZMod 61)) at hs
    change 61=7 → (22 : ZMod 61) ≠ 3 at h7
    change 61=11 → (22 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨4,![24,2,13,30],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (23 : ZMod 61)
    change (23 : ZMod 61) ≠ 0 at hp
    change (23 : ZMod 61)-1 ≠ 0 at ha
    change (23 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 61)+1)) at hr
    change IsSquare (3-(23 : ZMod 61)) at hs
    change 61=7 → (23 : ZMod 61) ≠ 3 at h7
    change 61=11 → (23 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨11,![3,14,24,12],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (24 : ZMod 61)
    change (24 : ZMod 61) ≠ 0 at hp
    change (24 : ZMod 61)-1 ≠ 0 at ha
    change (24 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 61)+1)) at hr
    change IsSquare (3-(24 : ZMod 61)) at hs
    change 61=7 → (24 : ZMod 61) ≠ 3 at h7
    change 61=11 → (24 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (50 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (25 : ZMod 61)
    change (25 : ZMod 61) ≠ 0 at hp
    change (25 : ZMod 61)-1 ≠ 0 at ha
    change (25 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 61)+1)) at hr
    change IsSquare (3-(25 : ZMod 61)) at hs
    change 61=7 → (25 : ZMod 61) ≠ 3 at h7
    change 61=11 → (25 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨4,![10,12,4,0],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (26 : ZMod 61)
    change (26 : ZMod 61) ≠ 0 at hp
    change (26 : ZMod 61)-1 ≠ 0 at ha
    change (26 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 61)+1)) at hr
    change IsSquare (3-(26 : ZMod 61)) at hs
    change 61=7 → (26 : ZMod 61) ≠ 3 at h7
    change 61=11 → (26 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (54 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (27 : ZMod 61)
    change (27 : ZMod 61) ≠ 0 at hp
    change (27 : ZMod 61)-1 ≠ 0 at ha
    change (27 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 61)+1)) at hr
    change IsSquare (3-(27 : ZMod 61)) at hs
    change 61=7 → (27 : ZMod 61) ≠ 3 at h7
    change 61=11 → (27 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (37 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (28 : ZMod 61)
    change (28 : ZMod 61) ≠ 0 at hp
    change (28 : ZMod 61)-1 ≠ 0 at ha
    change (28 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 61)+1)) at hr
    change IsSquare (3-(28 : ZMod 61)) at hs
    change 61=7 → (28 : ZMod 61) ≠ 3 at h7
    change 61=11 → (28 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨8,![23,16,20,1],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (29 : ZMod 61)
    change (29 : ZMod 61) ≠ 0 at hp
    change (29 : ZMod 61)-1 ≠ 0 at ha
    change (29 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 61)+1)) at hr
    change IsSquare (3-(29 : ZMod 61)) at hs
    change 61=7 → (29 : ZMod 61) ≠ 3 at h7
    change 61=11 → (29 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (30 : ZMod 61)
    change (30 : ZMod 61) ≠ 0 at hp
    change (30 : ZMod 61)-1 ≠ 0 at ha
    change (30 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 61)+1)) at hr
    change IsSquare (3-(30 : ZMod 61)) at hs
    change 61=7 → (30 : ZMod 61) ≠ 3 at h7
    change 61=11 → (30 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨35,![14,9,6,3],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (31 : ZMod 61)
    change (31 : ZMod 61) ≠ 0 at hp
    change (31 : ZMod 61)-1 ≠ 0 at ha
    change (31 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 61)+1)) at hr
    change IsSquare (3-(31 : ZMod 61)) at hs
    change 61=7 → (31 : ZMod 61) ≠ 3 at h7
    change 61=11 → (31 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (32 : ZMod 61)
    change (32 : ZMod 61) ≠ 0 at hp
    change (32 : ZMod 61)-1 ≠ 0 at ha
    change (32 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 61)+1)) at hr
    change IsSquare (3-(32 : ZMod 61)) at hs
    change 61=7 → (32 : ZMod 61) ≠ 3 at h7
    change 61=11 → (32 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (32 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (33 : ZMod 61)
    change (33 : ZMod 61) ≠ 0 at hp
    change (33 : ZMod 61)-1 ≠ 0 at ha
    change (33 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 61)+1)) at hr
    change IsSquare (3-(33 : ZMod 61)) at hs
    change 61=7 → (33 : ZMod 61) ≠ 3 at h7
    change 61=11 → (33 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (34 : ZMod 61)
    change (34 : ZMod 61) ≠ 0 at hp
    change (34 : ZMod 61)-1 ≠ 0 at ha
    change (34 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 61)+1)) at hr
    change IsSquare (3-(34 : ZMod 61)) at hs
    change 61=7 → (34 : ZMod 61) ≠ 3 at h7
    change 61=11 → (34 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (35 : ZMod 61)
    change (35 : ZMod 61) ≠ 0 at hp
    change (35 : ZMod 61)-1 ≠ 0 at ha
    change (35 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 61)+1)) at hr
    change IsSquare (3-(35 : ZMod 61)) at hs
    change 61=7 → (35 : ZMod 61) ≠ 3 at h7
    change 61=11 → (35 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (36 : ZMod 61)
    change (36 : ZMod 61) ≠ 0 at hp
    change (36 : ZMod 61)-1 ≠ 0 at ha
    change (36 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 61)+1)) at hr
    change IsSquare (3-(36 : ZMod 61)) at hs
    change 61=7 → (36 : ZMod 61) ≠ 3 at h7
    change 61=11 → (36 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (37 : ZMod 61)
    change (37 : ZMod 61) ≠ 0 at hp
    change (37 : ZMod 61)-1 ≠ 0 at ha
    change (37 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 61)+1)) at hr
    change IsSquare (3-(37 : ZMod 61)) at hs
    change 61=7 → (37 : ZMod 61) ≠ 3 at h7
    change 61=11 → (37 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨18,![19,2,23,25],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (38 : ZMod 61)
    change (38 : ZMod 61) ≠ 0 at hp
    change (38 : ZMod 61)-1 ≠ 0 at ha
    change (38 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 61)+1)) at hr
    change IsSquare (3-(38 : ZMod 61)) at hs
    change 61=7 → (38 : ZMod 61) ≠ 3 at h7
    change 61=11 → (38 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (39 : ZMod 61)
    change (39 : ZMod 61) ≠ 0 at hp
    change (39 : ZMod 61)-1 ≠ 0 at ha
    change (39 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 61)+1)) at hr
    change IsSquare (3-(39 : ZMod 61)) at hs
    change 61=7 → (39 : ZMod 61) ≠ 3 at h7
    change 61=11 → (39 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨4,![20,17,20,3],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (40 : ZMod 61)
    change (40 : ZMod 61) ≠ 0 at hp
    change (40 : ZMod 61)-1 ≠ 0 at ha
    change (40 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 61)+1)) at hr
    change IsSquare (3-(40 : ZMod 61)) at hs
    change 61=7 → (40 : ZMod 61) ≠ 3 at h7
    change 61=11 → (40 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (41 : ZMod 61)
    change (41 : ZMod 61) ≠ 0 at hp
    change (41 : ZMod 61)-1 ≠ 0 at ha
    change (41 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 61)+1)) at hr
    change IsSquare (3-(41 : ZMod 61)) at hs
    change 61=7 → (41 : ZMod 61) ≠ 3 at h7
    change 61=11 → (41 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (42 : ZMod 61)
    change (42 : ZMod 61) ≠ 0 at hp
    change (42 : ZMod 61)-1 ≠ 0 at ha
    change (42 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 61)+1)) at hr
    change IsSquare (3-(42 : ZMod 61)) at hs
    change 61=7 → (42 : ZMod 61) ≠ 3 at h7
    change 61=11 → (42 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨12,![4,29,9,13],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (43 : ZMod 61)
    change (43 : ZMod 61) ≠ 0 at hp
    change (43 : ZMod 61)-1 ≠ 0 at ha
    change (43 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((43 : ZMod 61)+1)) at hr
    change IsSquare (3-(43 : ZMod 61)) at hs
    change 61=7 → (43 : ZMod 61) ≠ 3 at h7
    change 61=11 → (43 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (44 : ZMod 61)
    change (44 : ZMod 61) ≠ 0 at hp
    change (44 : ZMod 61)-1 ≠ 0 at ha
    change (44 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((44 : ZMod 61)+1)) at hr
    change IsSquare (3-(44 : ZMod 61)) at hs
    change 61=7 → (44 : ZMod 61) ≠ 3 at h7
    change 61=11 → (44 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (45 : ZMod 61)
    change (45 : ZMod 61) ≠ 0 at hp
    change (45 : ZMod 61)-1 ≠ 0 at ha
    change (45 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((45 : ZMod 61)+1)) at hr
    change IsSquare (3-(45 : ZMod 61)) at hs
    change 61=7 → (45 : ZMod 61) ≠ 3 at h7
    change 61=11 → (45 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (46 : ZMod 61)
    change (46 : ZMod 61) ≠ 0 at hp
    change (46 : ZMod 61)-1 ≠ 0 at ha
    change (46 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((46 : ZMod 61)+1)) at hr
    change IsSquare (3-(46 : ZMod 61)) at hs
    change 61=7 → (46 : ZMod 61) ≠ 3 at h7
    change 61=11 → (46 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (47 : ZMod 61)
    change (47 : ZMod 61) ≠ 0 at hp
    change (47 : ZMod 61)-1 ≠ 0 at ha
    change (47 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((47 : ZMod 61)+1)) at hr
    change IsSquare (3-(47 : ZMod 61)) at hs
    change 61=7 → (47 : ZMod 61) ≠ 3 at h7
    change 61=11 → (47 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (48 : ZMod 61)
    change (48 : ZMod 61) ≠ 0 at hp
    change (48 : ZMod 61)-1 ≠ 0 at ha
    change (48 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((48 : ZMod 61)+1)) at hr
    change IsSquare (3-(48 : ZMod 61)) at hs
    change 61=7 → (48 : ZMod 61) ≠ 3 at h7
    change 61=11 → (48 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (37 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (49 : ZMod 61)
    change (49 : ZMod 61) ≠ 0 at hp
    change (49 : ZMod 61)-1 ≠ 0 at ha
    change (49 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((49 : ZMod 61)+1)) at hr
    change IsSquare (3-(49 : ZMod 61)) at hs
    change 61=7 → (49 : ZMod 61) ≠ 3 at h7
    change 61=11 → (49 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨12,![10,18,18,4],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (50 : ZMod 61)
    change (50 : ZMod 61) ≠ 0 at hp
    change (50 : ZMod 61)-1 ≠ 0 at ha
    change (50 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((50 : ZMod 61)+1)) at hr
    change IsSquare (3-(50 : ZMod 61)) at hs
    change 61=7 → (50 : ZMod 61) ≠ 3 at h7
    change 61=11 → (50 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨8,![20,25,8,4],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (51 : ZMod 61)
    change (51 : ZMod 61) ≠ 0 at hp
    change (51 : ZMod 61)-1 ≠ 0 at ha
    change (51 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((51 : ZMod 61)+1)) at hr
    change IsSquare (3-(51 : ZMod 61)) at hs
    change 61=7 → (51 : ZMod 61) ≠ 3 at h7
    change 61=11 → (51 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (52 : ZMod 61)
    change (52 : ZMod 61) ≠ 0 at hp
    change (52 : ZMod 61)-1 ≠ 0 at ha
    change (52 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((52 : ZMod 61)+1)) at hr
    change IsSquare (3-(52 : ZMod 61)) at hs
    change 61=7 → (52 : ZMod 61) ≠ 3 at h7
    change 61=11 → (52 : ZMod 61) ≠ 5 at h11
    apply Or.inl
    refine ⟨4,![5,1,15,14],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (53 : ZMod 61)
    change (53 : ZMod 61) ≠ 0 at hp
    change (53 : ZMod 61)-1 ≠ 0 at ha
    change (53 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((53 : ZMod 61)+1)) at hr
    change IsSquare (3-(53 : ZMod 61)) at hs
    change 61=7 → (53 : ZMod 61) ≠ 3 at h7
    change 61=11 → (53 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (54 : ZMod 61)
    change (54 : ZMod 61) ≠ 0 at hp
    change (54 : ZMod 61)-1 ≠ 0 at ha
    change (54 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((54 : ZMod 61)+1)) at hr
    change IsSquare (3-(54 : ZMod 61)) at hs
    change 61=7 → (54 : ZMod 61) ≠ 3 at h7
    change 61=11 → (54 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (55 : ZMod 61)
    change (55 : ZMod 61) ≠ 0 at hp
    change (55 : ZMod 61)-1 ≠ 0 at ha
    change (55 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((55 : ZMod 61)+1)) at hr
    change IsSquare (3-(55 : ZMod 61)) at hs
    change 61=7 → (55 : ZMod 61) ≠ 3 at h7
    change 61=11 → (55 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (51 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (56 : ZMod 61)
    change (56 : ZMod 61) ≠ 0 at hp
    change (56 : ZMod 61)-1 ≠ 0 at ha
    change (56 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((56 : ZMod 61)+1)) at hr
    change IsSquare (3-(56 : ZMod 61)) at hs
    change 61=7 → (56 : ZMod 61) ≠ 3 at h7
    change 61=11 → (56 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (53 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (57 : ZMod 61)
    change (57 : ZMod 61) ≠ 0 at hp
    change (57 : ZMod 61)-1 ≠ 0 at ha
    change (57 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((57 : ZMod 61)+1)) at hr
    change IsSquare (3-(57 : ZMod 61)) at hs
    change 61=7 → (57 : ZMod 61) ≠ 3 at h7
    change 61=11 → (57 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (55 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (58 : ZMod 61)
    change (58 : ZMod 61) ≠ 0 at hp
    change (58 : ZMod 61)-1 ≠ 0 at ha
    change (58 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((58 : ZMod 61)+1)) at hr
    change IsSquare (3-(58 : ZMod 61)) at hs
    change 61=7 → (58 : ZMod 61) ≠ 3 at h7
    change 61=11 → (58 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (59 : ZMod 61)
    change (59 : ZMod 61) ≠ 0 at hp
    change (59 : ZMod 61)-1 ≠ 0 at ha
    change (59 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((59 : ZMod 61)+1)) at hr
    change IsSquare (3-(59 : ZMod 61)) at hs
    change 61=7 → (59 : ZMod 61) ≠ 3 at h7
    change 61=11 → (59 : ZMod 61) ≠ 5 at h11
    have hn : ¬IsSquare (59 : ZMod 61) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (60 : ZMod 61)
    change (60 : ZMod 61) ≠ 0 at hp
    change (60 : ZMod 61)-1 ≠ 0 at ha
    change (60 : ZMod 61)+1 ≠ 0 at hb
    change IsSquare (2*((60 : ZMod 61)+1)) at hr
    change IsSquare (3-(60 : ZMod 61)) at hs
    change 61=7 → (60 : ZMod 61) ≠ 3 at h7
    change 61=11 → (60 : ZMod 61) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts61

private instance prime67 : Fact (Nat.Prime 67) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts67 (p : ZMod 67) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 67=7 → p ≠ 3) (h11 : 67=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 67)
    change (0 : ZMod 67) ≠ 0 at hp
    change (0 : ZMod 67)-1 ≠ 0 at ha
    change (0 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 67)+1)) at hr
    change IsSquare (3-(0 : ZMod 67)) at hs
    change 67=7 → (0 : ZMod 67) ≠ 3 at h7
    change 67=11 → (0 : ZMod 67) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 67)
    change (1 : ZMod 67) ≠ 0 at hp
    change (1 : ZMod 67)-1 ≠ 0 at ha
    change (1 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 67)+1)) at hr
    change IsSquare (3-(1 : ZMod 67)) at hs
    change 67=7 → (1 : ZMod 67) ≠ 3 at h7
    change 67=11 → (1 : ZMod 67) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 67)
    change (2 : ZMod 67) ≠ 0 at hp
    change (2 : ZMod 67)-1 ≠ 0 at ha
    change (2 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 67)+1)) at hr
    change IsSquare (3-(2 : ZMod 67)) at hs
    change 67=7 → (2 : ZMod 67) ≠ 3 at h7
    change 67=11 → (2 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![26,2,15,26],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (3 : ZMod 67)
    change (3 : ZMod 67) ≠ 0 at hp
    change (3 : ZMod 67)-1 ≠ 0 at ha
    change (3 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 67)+1)) at hr
    change IsSquare (3-(3 : ZMod 67)) at hs
    change 67=7 → (3 : ZMod 67) ≠ 3 at h7
    change 67=11 → (3 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 67)
    change (4 : ZMod 67) ≠ 0 at hp
    change (4 : ZMod 67)-1 ≠ 0 at ha
    change (4 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 67)+1)) at hr
    change IsSquare (3-(4 : ZMod 67)) at hs
    change 67=7 → (4 : ZMod 67) ≠ 3 at h7
    change 67=11 → (4 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (66 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (5 : ZMod 67)
    change (5 : ZMod 67) ≠ 0 at hp
    change (5 : ZMod 67)-1 ≠ 0 at ha
    change (5 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 67)+1)) at hr
    change IsSquare (3-(5 : ZMod 67)) at hs
    change 67=7 → (5 : ZMod 67) ≠ 3 at h7
    change 67=11 → (5 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (6 : ZMod 67)
    change (6 : ZMod 67) ≠ 0 at hp
    change (6 : ZMod 67)-1 ≠ 0 at ha
    change (6 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 67)+1)) at hr
    change IsSquare (3-(6 : ZMod 67)) at hs
    change 67=7 → (6 : ZMod 67) ≠ 3 at h7
    change 67=11 → (6 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![31,26,31,22],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (7 : ZMod 67)
    change (7 : ZMod 67) ≠ 0 at hp
    change (7 : ZMod 67)-1 ≠ 0 at ha
    change (7 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 67)+1)) at hr
    change IsSquare (3-(7 : ZMod 67)) at hs
    change 67=7 → (7 : ZMod 67) ≠ 3 at h7
    change 67=11 → (7 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (63 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (8 : ZMod 67)
    change (8 : ZMod 67) ≠ 0 at hp
    change (8 : ZMod 67)-1 ≠ 0 at ha
    change (8 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 67)+1)) at hr
    change IsSquare (3-(8 : ZMod 67)) at hs
    change 67=7 → (8 : ZMod 67) ≠ 3 at h7
    change 67=11 → (8 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (9 : ZMod 67)
    change (9 : ZMod 67) ≠ 0 at hp
    change (9 : ZMod 67)-1 ≠ 0 at ha
    change (9 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 67)+1)) at hr
    change IsSquare (3-(9 : ZMod 67)) at hs
    change 67=7 → (9 : ZMod 67) ≠ 3 at h7
    change 67=11 → (9 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (10 : ZMod 67)
    change (10 : ZMod 67) ≠ 0 at hp
    change (10 : ZMod 67)-1 ≠ 0 at ha
    change (10 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 67)+1)) at hr
    change IsSquare (3-(10 : ZMod 67)) at hs
    change 67=7 → (10 : ZMod 67) ≠ 3 at h7
    change 67=11 → (10 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨9,![31,12,32,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (11 : ZMod 67)
    change (11 : ZMod 67) ≠ 0 at hp
    change (11 : ZMod 67)-1 ≠ 0 at ha
    change (11 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 67)+1)) at hr
    change IsSquare (3-(11 : ZMod 67)) at hs
    change 67=7 → (11 : ZMod 67) ≠ 3 at h7
    change 67=11 → (11 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨8,![17,26,22,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (12 : ZMod 67)
    change (12 : ZMod 67) ≠ 0 at hp
    change (12 : ZMod 67)-1 ≠ 0 at ha
    change (12 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 67)+1)) at hr
    change IsSquare (3-(12 : ZMod 67)) at hs
    change 67=7 → (12 : ZMod 67) ≠ 3 at h7
    change 67=11 → (12 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (58 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (13 : ZMod 67)
    change (13 : ZMod 67) ≠ 0 at hp
    change (13 : ZMod 67)-1 ≠ 0 at ha
    change (13 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 67)+1)) at hr
    change IsSquare (3-(13 : ZMod 67)) at hs
    change 67=7 → (13 : ZMod 67) ≠ 3 at h7
    change 67=11 → (13 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (14 : ZMod 67)
    change (14 : ZMod 67) ≠ 0 at hp
    change (14 : ZMod 67)-1 ≠ 0 at ha
    change (14 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 67)+1)) at hr
    change IsSquare (3-(14 : ZMod 67)) at hs
    change 67=7 → (14 : ZMod 67) ≠ 3 at h7
    change 67=11 → (14 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 67)
    change (15 : ZMod 67) ≠ 0 at hp
    change (15 : ZMod 67)-1 ≠ 0 at ha
    change (15 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 67)+1)) at hr
    change IsSquare (3-(15 : ZMod 67)) at hs
    change 67=7 → (15 : ZMod 67) ≠ 3 at h7
    change 67=11 → (15 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (32 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (16 : ZMod 67)
    change (16 : ZMod 67) ≠ 0 at hp
    change (16 : ZMod 67)-1 ≠ 0 at ha
    change (16 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 67)+1)) at hr
    change IsSquare (3-(16 : ZMod 67)) at hs
    change 67=7 → (16 : ZMod 67) ≠ 3 at h7
    change 67=11 → (16 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 67)
    change (17 : ZMod 67) ≠ 0 at hp
    change (17 : ZMod 67)-1 ≠ 0 at ha
    change (17 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 67)+1)) at hr
    change IsSquare (3-(17 : ZMod 67)) at hs
    change 67=7 → (17 : ZMod 67) ≠ 3 at h7
    change 67=11 → (17 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (53 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (18 : ZMod 67)
    change (18 : ZMod 67) ≠ 0 at hp
    change (18 : ZMod 67)-1 ≠ 0 at ha
    change (18 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 67)+1)) at hr
    change IsSquare (3-(18 : ZMod 67)) at hs
    change 67=7 → (18 : ZMod 67) ≠ 3 at h7
    change 67=11 → (18 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (38 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (19 : ZMod 67)
    change (19 : ZMod 67) ≠ 0 at hp
    change (19 : ZMod 67)-1 ≠ 0 at ha
    change (19 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 67)+1)) at hr
    change IsSquare (3-(19 : ZMod 67)) at hs
    change 67=7 → (19 : ZMod 67) ≠ 3 at h7
    change 67=11 → (19 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (51 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (20 : ZMod 67)
    change (20 : ZMod 67) ≠ 0 at hp
    change (20 : ZMod 67)-1 ≠ 0 at ha
    change (20 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 67)+1)) at hr
    change IsSquare (3-(20 : ZMod 67)) at hs
    change 67=7 → (20 : ZMod 67) ≠ 3 at h7
    change 67=11 → (20 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (42 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (21 : ZMod 67)
    change (21 : ZMod 67) ≠ 0 at hp
    change (21 : ZMod 67)-1 ≠ 0 at ha
    change (21 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 67)+1)) at hr
    change IsSquare (3-(21 : ZMod 67)) at hs
    change 67=7 → (21 : ZMod 67) ≠ 3 at h7
    change 67=11 → (21 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (44 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (22 : ZMod 67)
    change (22 : ZMod 67) ≠ 0 at hp
    change (22 : ZMod 67)-1 ≠ 0 at ha
    change (22 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 67)+1)) at hr
    change IsSquare (3-(22 : ZMod 67)) at hs
    change 67=7 → (22 : ZMod 67) ≠ 3 at h7
    change 67=11 → (22 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (46 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (23 : ZMod 67)
    change (23 : ZMod 67) ≠ 0 at hp
    change (23 : ZMod 67)-1 ≠ 0 at ha
    change (23 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 67)+1)) at hr
    change IsSquare (3-(23 : ZMod 67)) at hs
    change 67=7 → (23 : ZMod 67) ≠ 3 at h7
    change 67=11 → (23 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (48 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (24 : ZMod 67)
    change (24 : ZMod 67) ≠ 0 at hp
    change (24 : ZMod 67)-1 ≠ 0 at ha
    change (24 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 67)+1)) at hr
    change IsSquare (3-(24 : ZMod 67)) at hs
    change 67=7 → (24 : ZMod 67) ≠ 3 at h7
    change 67=11 → (24 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (50 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (25 : ZMod 67)
    change (25 : ZMod 67) ≠ 0 at hp
    change (25 : ZMod 67)-1 ≠ 0 at ha
    change (25 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 67)+1)) at hr
    change IsSquare (3-(25 : ZMod 67)) at hs
    change 67=7 → (25 : ZMod 67) ≠ 3 at h7
    change 67=11 → (25 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (52 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (26 : ZMod 67)
    change (26 : ZMod 67) ≠ 0 at hp
    change (26 : ZMod 67)-1 ≠ 0 at ha
    change (26 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 67)+1)) at hr
    change IsSquare (3-(26 : ZMod 67)) at hs
    change 67=7 → (26 : ZMod 67) ≠ 3 at h7
    change 67=11 → (26 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (44 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (27 : ZMod 67)
    change (27 : ZMod 67) ≠ 0 at hp
    change (27 : ZMod 67)-1 ≠ 0 at ha
    change (27 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 67)+1)) at hr
    change IsSquare (3-(27 : ZMod 67)) at hs
    change 67=7 → (27 : ZMod 67) ≠ 3 at h7
    change 67=11 → (27 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (28 : ZMod 67)
    change (28 : ZMod 67) ≠ 0 at hp
    change (28 : ZMod 67)-1 ≠ 0 at ha
    change (28 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 67)+1)) at hr
    change IsSquare (3-(28 : ZMod 67)) at hs
    change 67=7 → (28 : ZMod 67) ≠ 3 at h7
    change 67=11 → (28 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (58 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (29 : ZMod 67)
    change (29 : ZMod 67) ≠ 0 at hp
    change (29 : ZMod 67)-1 ≠ 0 at ha
    change (29 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 67)+1)) at hr
    change IsSquare (3-(29 : ZMod 67)) at hs
    change 67=7 → (29 : ZMod 67) ≠ 3 at h7
    change 67=11 → (29 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (41 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (30 : ZMod 67)
    change (30 : ZMod 67) ≠ 0 at hp
    change (30 : ZMod 67)-1 ≠ 0 at ha
    change (30 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 67)+1)) at hr
    change IsSquare (3-(30 : ZMod 67)) at hs
    change 67=7 → (30 : ZMod 67) ≠ 3 at h7
    change 67=11 → (30 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨8,![21,2,25,14],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (31 : ZMod 67)
    change (31 : ZMod 67) ≠ 0 at hp
    change (31 : ZMod 67)-1 ≠ 0 at ha
    change (31 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 67)+1)) at hr
    change IsSquare (3-(31 : ZMod 67)) at hs
    change 67=7 → (31 : ZMod 67) ≠ 3 at h7
    change 67=11 → (31 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨18,![25,22,12,6],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (32 : ZMod 67)
    change (32 : ZMod 67) ≠ 0 at hp
    change (32 : ZMod 67)-1 ≠ 0 at ha
    change (32 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 67)+1)) at hr
    change IsSquare (3-(32 : ZMod 67)) at hs
    change 67=7 → (32 : ZMod 67) ≠ 3 at h7
    change 67=11 → (32 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (66 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (33 : ZMod 67)
    change (33 : ZMod 67) ≠ 0 at hp
    change (33 : ZMod 67)-1 ≠ 0 at ha
    change (33 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 67)+1)) at hr
    change IsSquare (3-(33 : ZMod 67)) at hs
    change 67=7 → (33 : ZMod 67) ≠ 3 at h7
    change 67=11 → (33 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨16,![27,25,33,12],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (34 : ZMod 67)
    change (34 : ZMod 67) ≠ 0 at hp
    change (34 : ZMod 67)-1 ≠ 0 at ha
    change (34 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 67)+1)) at hr
    change IsSquare (3-(34 : ZMod 67)) at hs
    change 67=7 → (34 : ZMod 67) ≠ 3 at h7
    change 67=11 → (34 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (35 : ZMod 67)
    change (35 : ZMod 67) ≠ 0 at hp
    change (35 : ZMod 67)-1 ≠ 0 at ha
    change (35 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 67)+1)) at hr
    change IsSquare (3-(35 : ZMod 67)) at hs
    change 67=7 → (35 : ZMod 67) ≠ 3 at h7
    change 67=11 → (35 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (36 : ZMod 67)
    change (36 : ZMod 67) ≠ 0 at hp
    change (36 : ZMod 67)-1 ≠ 0 at ha
    change (36 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 67)+1)) at hr
    change IsSquare (3-(36 : ZMod 67)) at hs
    change 67=7 → (36 : ZMod 67) ≠ 3 at h7
    change 67=11 → (36 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (37 : ZMod 67)
    change (37 : ZMod 67) ≠ 0 at hp
    change (37 : ZMod 67)-1 ≠ 0 at ha
    change (37 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 67)+1)) at hr
    change IsSquare (3-(37 : ZMod 67)) at hs
    change 67=7 → (37 : ZMod 67) ≠ 3 at h7
    change 67=11 → (37 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨14,![7,20,1,26],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (38 : ZMod 67)
    change (38 : ZMod 67) ≠ 0 at hp
    change (38 : ZMod 67)-1 ≠ 0 at ha
    change (38 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 67)+1)) at hr
    change IsSquare (3-(38 : ZMod 67)) at hs
    change 67=7 → (38 : ZMod 67) ≠ 3 at h7
    change 67=11 → (38 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (39 : ZMod 67)
    change (39 : ZMod 67) ≠ 0 at hp
    change (39 : ZMod 67)-1 ≠ 0 at ha
    change (39 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 67)+1)) at hr
    change IsSquare (3-(39 : ZMod 67)) at hs
    change 67=7 → (39 : ZMod 67) ≠ 3 at h7
    change 67=11 → (39 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (40 : ZMod 67)
    change (40 : ZMod 67) ≠ 0 at hp
    change (40 : ZMod 67)-1 ≠ 0 at ha
    change (40 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 67)+1)) at hr
    change IsSquare (3-(40 : ZMod 67)) at hs
    change 67=7 → (40 : ZMod 67) ≠ 3 at h7
    change 67=11 → (40 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (41 : ZMod 67)
    change (41 : ZMod 67) ≠ 0 at hp
    change (41 : ZMod 67)-1 ≠ 0 at ha
    change (41 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 67)+1)) at hr
    change IsSquare (3-(41 : ZMod 67)) at hs
    change 67=7 → (41 : ZMod 67) ≠ 3 at h7
    change 67=11 → (41 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨13,![8,25,29,19],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (42 : ZMod 67)
    change (42 : ZMod 67) ≠ 0 at hp
    change (42 : ZMod 67)-1 ≠ 0 at ha
    change (42 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 67)+1)) at hr
    change IsSquare (3-(42 : ZMod 67)) at hs
    change 67=7 → (42 : ZMod 67) ≠ 3 at h7
    change 67=11 → (42 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (43 : ZMod 67)
    change (43 : ZMod 67) ≠ 0 at hp
    change (43 : ZMod 67)-1 ≠ 0 at ha
    change (43 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((43 : ZMod 67)+1)) at hr
    change IsSquare (3-(43 : ZMod 67)) at hs
    change 67=7 → (43 : ZMod 67) ≠ 3 at h7
    change 67=11 → (43 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (44 : ZMod 67)
    change (44 : ZMod 67) ≠ 0 at hp
    change (44 : ZMod 67)-1 ≠ 0 at ha
    change (44 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((44 : ZMod 67)+1)) at hr
    change IsSquare (3-(44 : ZMod 67)) at hs
    change 67=7 → (44 : ZMod 67) ≠ 3 at h7
    change 67=11 → (44 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨5,![32,3,2,27],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (45 : ZMod 67)
    change (45 : ZMod 67) ≠ 0 at hp
    change (45 : ZMod 67)-1 ≠ 0 at ha
    change (45 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((45 : ZMod 67)+1)) at hr
    change IsSquare (3-(45 : ZMod 67)) at hs
    change 67=7 → (45 : ZMod 67) ≠ 3 at h7
    change 67=11 → (45 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨5,![15,33,4,20],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (46 : ZMod 67)
    change (46 : ZMod 67) ≠ 0 at hp
    change (46 : ZMod 67)-1 ≠ 0 at ha
    change (46 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((46 : ZMod 67)+1)) at hr
    change IsSquare (3-(46 : ZMod 67)) at hs
    change 67=7 → (46 : ZMod 67) ≠ 3 at h7
    change 67=11 → (46 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (47 : ZMod 67)
    change (47 : ZMod 67) ≠ 0 at hp
    change (47 : ZMod 67)-1 ≠ 0 at ha
    change (47 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((47 : ZMod 67)+1)) at hr
    change IsSquare (3-(47 : ZMod 67)) at hs
    change 67=7 → (47 : ZMod 67) ≠ 3 at h7
    change 67=11 → (47 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![13,22,14,1],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (48 : ZMod 67)
    change (48 : ZMod 67) ≠ 0 at hp
    change (48 : ZMod 67)-1 ≠ 0 at ha
    change (48 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((48 : ZMod 67)+1)) at hr
    change IsSquare (3-(48 : ZMod 67)) at hs
    change 67=7 → (48 : ZMod 67) ≠ 3 at h7
    change 67=11 → (48 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (49 : ZMod 67)
    change (49 : ZMod 67) ≠ 0 at hp
    change (49 : ZMod 67)-1 ≠ 0 at ha
    change (49 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((49 : ZMod 67)+1)) at hr
    change IsSquare (3-(49 : ZMod 67)) at hs
    change 67=7 → (49 : ZMod 67) ≠ 3 at h7
    change 67=11 → (49 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![20,2,27,10],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (50 : ZMod 67)
    change (50 : ZMod 67) ≠ 0 at hp
    change (50 : ZMod 67)-1 ≠ 0 at ha
    change (50 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((50 : ZMod 67)+1)) at hr
    change IsSquare (3-(50 : ZMod 67)) at hs
    change 67=7 → (50 : ZMod 67) ≠ 3 at h7
    change 67=11 → (50 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (51 : ZMod 67)
    change (51 : ZMod 67) ≠ 0 at hp
    change (51 : ZMod 67)-1 ≠ 0 at ha
    change (51 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((51 : ZMod 67)+1)) at hr
    change IsSquare (3-(51 : ZMod 67)) at hs
    change 67=7 → (51 : ZMod 67) ≠ 3 at h7
    change 67=11 → (51 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨18,![28,5,10,9],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (52 : ZMod 67)
    change (52 : ZMod 67) ≠ 0 at hp
    change (52 : ZMod 67)-1 ≠ 0 at ha
    change (52 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((52 : ZMod 67)+1)) at hr
    change IsSquare (3-(52 : ZMod 67)) at hs
    change 67=7 → (52 : ZMod 67) ≠ 3 at h7
    change 67=11 → (52 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (53 : ZMod 67)
    change (53 : ZMod 67) ≠ 0 at hp
    change (53 : ZMod 67)-1 ≠ 0 at ha
    change (53 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((53 : ZMod 67)+1)) at hr
    change IsSquare (3-(53 : ZMod 67)) at hs
    change 67=7 → (53 : ZMod 67) ≠ 3 at h7
    change 67=11 → (53 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (41 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (54 : ZMod 67)
    change (54 : ZMod 67) ≠ 0 at hp
    change (54 : ZMod 67)-1 ≠ 0 at ha
    change (54 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((54 : ZMod 67)+1)) at hr
    change IsSquare (3-(54 : ZMod 67)) at hs
    change 67=7 → (54 : ZMod 67) ≠ 3 at h7
    change 67=11 → (54 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (55 : ZMod 67)
    change (55 : ZMod 67) ≠ 0 at hp
    change (55 : ZMod 67)-1 ≠ 0 at ha
    change (55 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((55 : ZMod 67)+1)) at hr
    change IsSquare (3-(55 : ZMod 67)) at hs
    change 67=7 → (55 : ZMod 67) ≠ 3 at h7
    change 67=11 → (55 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (45 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (56 : ZMod 67)
    change (56 : ZMod 67) ≠ 0 at hp
    change (56 : ZMod 67)-1 ≠ 0 at ha
    change (56 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((56 : ZMod 67)+1)) at hr
    change IsSquare (3-(56 : ZMod 67)) at hs
    change 67=7 → (56 : ZMod 67) ≠ 3 at h7
    change 67=11 → (56 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨9,![13,3,1,4],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (57 : ZMod 67)
    change (57 : ZMod 67) ≠ 0 at hp
    change (57 : ZMod 67)-1 ≠ 0 at ha
    change (57 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((57 : ZMod 67)+1)) at hr
    change IsSquare (3-(57 : ZMod 67)) at hs
    change 67=7 → (57 : ZMod 67) ≠ 3 at h7
    change 67=11 → (57 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (58 : ZMod 67)
    change (58 : ZMod 67) ≠ 0 at hp
    change (58 : ZMod 67)-1 ≠ 0 at ha
    change (58 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((58 : ZMod 67)+1)) at hr
    change IsSquare (3-(58 : ZMod 67)) at hs
    change 67=7 → (58 : ZMod 67) ≠ 3 at h7
    change 67=11 → (58 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (51 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (59 : ZMod 67)
    change (59 : ZMod 67) ≠ 0 at hp
    change (59 : ZMod 67)-1 ≠ 0 at ha
    change (59 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((59 : ZMod 67)+1)) at hr
    change IsSquare (3-(59 : ZMod 67)) at hs
    change 67=7 → (59 : ZMod 67) ≠ 3 at h7
    change 67=11 → (59 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (53 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (60 : ZMod 67)
    change (60 : ZMod 67) ≠ 0 at hp
    change (60 : ZMod 67)-1 ≠ 0 at ha
    change (60 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((60 : ZMod 67)+1)) at hr
    change IsSquare (3-(60 : ZMod 67)) at hs
    change 67=7 → (60 : ZMod 67) ≠ 3 at h7
    change 67=11 → (60 : ZMod 67) ≠ 5 at h11
    apply Or.inl
    refine ⟨9,![2,26,9,18],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (61 : ZMod 67)
    change (61 : ZMod 67) ≠ 0 at hp
    change (61 : ZMod 67)-1 ≠ 0 at ha
    change (61 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((61 : ZMod 67)+1)) at hr
    change IsSquare (3-(61 : ZMod 67)) at hs
    change 67=7 → (61 : ZMod 67) ≠ 3 at h7
    change 67=11 → (61 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (57 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (62 : ZMod 67)
    change (62 : ZMod 67) ≠ 0 at hp
    change (62 : ZMod 67)-1 ≠ 0 at ha
    change (62 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((62 : ZMod 67)+1)) at hr
    change IsSquare (3-(62 : ZMod 67)) at hs
    change 67=7 → (62 : ZMod 67) ≠ 3 at h7
    change 67=11 → (62 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (63 : ZMod 67)
    change (63 : ZMod 67) ≠ 0 at hp
    change (63 : ZMod 67)-1 ≠ 0 at ha
    change (63 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((63 : ZMod 67)+1)) at hr
    change IsSquare (3-(63 : ZMod 67)) at hs
    change 67=7 → (63 : ZMod 67) ≠ 3 at h7
    change 67=11 → (63 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (61 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (64 : ZMod 67)
    change (64 : ZMod 67) ≠ 0 at hp
    change (64 : ZMod 67)-1 ≠ 0 at ha
    change (64 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((64 : ZMod 67)+1)) at hr
    change IsSquare (3-(64 : ZMod 67)) at hs
    change 67=7 → (64 : ZMod 67) ≠ 3 at h7
    change 67=11 → (64 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (63 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (65 : ZMod 67)
    change (65 : ZMod 67) ≠ 0 at hp
    change (65 : ZMod 67)-1 ≠ 0 at ha
    change (65 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((65 : ZMod 67)+1)) at hr
    change IsSquare (3-(65 : ZMod 67)) at hs
    change 67=7 → (65 : ZMod 67) ≠ 3 at h7
    change 67=11 → (65 : ZMod 67) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 67) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (66 : ZMod 67)
    change (66 : ZMod 67) ≠ 0 at hp
    change (66 : ZMod 67)-1 ≠ 0 at ha
    change (66 : ZMod 67)+1 ≠ 0 at hb
    change IsSquare (2*((66 : ZMod 67)+1)) at hr
    change IsSquare (3-(66 : ZMod 67)) at hs
    change 67=7 → (66 : ZMod 67) ≠ 3 at h7
    change 67=11 → (66 : ZMod 67) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts67

private instance prime71 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts71 (p : ZMod 71) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 71=7 → p ≠ 3) (h11 : 71=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 71)
    change (0 : ZMod 71) ≠ 0 at hp
    change (0 : ZMod 71)-1 ≠ 0 at ha
    change (0 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 71)+1)) at hr
    change IsSquare (3-(0 : ZMod 71)) at hs
    change 71=7 → (0 : ZMod 71) ≠ 3 at h7
    change 71=11 → (0 : ZMod 71) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 71)
    change (1 : ZMod 71) ≠ 0 at hp
    change (1 : ZMod 71)-1 ≠ 0 at ha
    change (1 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 71)+1)) at hr
    change IsSquare (3-(1 : ZMod 71)) at hs
    change 71=7 → (1 : ZMod 71) ≠ 3 at h7
    change 71=11 → (1 : ZMod 71) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 71)
    change (2 : ZMod 71) ≠ 0 at hp
    change (2 : ZMod 71)-1 ≠ 0 at ha
    change (2 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 71)+1)) at hr
    change IsSquare (3-(2 : ZMod 71)) at hs
    change 71=7 → (2 : ZMod 71) ≠ 3 at h7
    change 71=11 → (2 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![12,0,15,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (3 : ZMod 71)
    change (3 : ZMod 71) ≠ 0 at hp
    change (3 : ZMod 71)-1 ≠ 0 at ha
    change (3 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 71)+1)) at hr
    change IsSquare (3-(3 : ZMod 71)) at hs
    change 71=7 → (3 : ZMod 71) ≠ 3 at h7
    change 71=11 → (3 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![28,0,4,19],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (4 : ZMod 71)
    change (4 : ZMod 71) ≠ 0 at hp
    change (4 : ZMod 71)-1 ≠ 0 at ha
    change (4 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 71)+1)) at hr
    change IsSquare (3-(4 : ZMod 71)) at hs
    change 71=7 → (4 : ZMod 71) ≠ 3 at h7
    change 71=11 → (4 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (70 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (5 : ZMod 71)
    change (5 : ZMod 71) ≠ 0 at hp
    change (5 : ZMod 71)-1 ≠ 0 at ha
    change (5 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 71)+1)) at hr
    change IsSquare (3-(5 : ZMod 71)) at hs
    change 71=7 → (5 : ZMod 71) ≠ 3 at h7
    change 71=11 → (5 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (69 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (6 : ZMod 71)
    change (6 : ZMod 71) ≠ 0 at hp
    change (6 : ZMod 71)-1 ≠ 0 at ha
    change (6 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 71)+1)) at hr
    change IsSquare (3-(6 : ZMod 71)) at hs
    change 71=7 → (6 : ZMod 71) ≠ 3 at h7
    change 71=11 → (6 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 71)
    change (7 : ZMod 71) ≠ 0 at hp
    change (7 : ZMod 71)-1 ≠ 0 at ha
    change (7 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 71)+1)) at hr
    change IsSquare (3-(7 : ZMod 71)) at hs
    change 71=7 → (7 : ZMod 71) ≠ 3 at h7
    change 71=11 → (7 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (67 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (8 : ZMod 71)
    change (8 : ZMod 71) ≠ 0 at hp
    change (8 : ZMod 71)-1 ≠ 0 at ha
    change (8 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 71)+1)) at hr
    change IsSquare (3-(8 : ZMod 71)) at hs
    change 71=7 → (8 : ZMod 71) ≠ 3 at h7
    change 71=11 → (8 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (66 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (9 : ZMod 71)
    change (9 : ZMod 71) ≠ 0 at hp
    change (9 : ZMod 71)-1 ≠ 0 at ha
    change (9 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 71)+1)) at hr
    change IsSquare (3-(9 : ZMod 71)) at hs
    change 71=7 → (9 : ZMod 71) ≠ 3 at h7
    change 71=11 → (9 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (65 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (10 : ZMod 71)
    change (10 : ZMod 71) ≠ 0 at hp
    change (10 : ZMod 71)-1 ≠ 0 at ha
    change (10 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 71)+1)) at hr
    change IsSquare (3-(10 : ZMod 71)) at hs
    change 71=7 → (10 : ZMod 71) ≠ 3 at h7
    change 71=11 → (10 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 71)
    change (11 : ZMod 71) ≠ 0 at hp
    change (11 : ZMod 71)-1 ≠ 0 at ha
    change (11 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 71)+1)) at hr
    change IsSquare (3-(11 : ZMod 71)) at hs
    change 71=7 → (11 : ZMod 71) ≠ 3 at h7
    change 71=11 → (11 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (63 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (12 : ZMod 71)
    change (12 : ZMod 71) ≠ 0 at hp
    change (12 : ZMod 71)-1 ≠ 0 at ha
    change (12 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 71)+1)) at hr
    change IsSquare (3-(12 : ZMod 71)) at hs
    change 71=7 → (12 : ZMod 71) ≠ 3 at h7
    change 71=11 → (12 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (13 : ZMod 71)
    change (13 : ZMod 71) ≠ 0 at hp
    change (13 : ZMod 71)-1 ≠ 0 at ha
    change (13 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 71)+1)) at hr
    change IsSquare (3-(13 : ZMod 71)) at hs
    change 71=7 → (13 : ZMod 71) ≠ 3 at h7
    change 71=11 → (13 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (14 : ZMod 71)
    change (14 : ZMod 71) ≠ 0 at hp
    change (14 : ZMod 71)-1 ≠ 0 at ha
    change (14 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 71)+1)) at hr
    change IsSquare (3-(14 : ZMod 71)) at hs
    change 71=7 → (14 : ZMod 71) ≠ 3 at h7
    change 71=11 → (14 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,20,32,21],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (15 : ZMod 71)
    change (15 : ZMod 71) ≠ 0 at hp
    change (15 : ZMod 71)-1 ≠ 0 at ha
    change (15 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 71)+1)) at hr
    change IsSquare (3-(15 : ZMod 71)) at hs
    change 71=7 → (15 : ZMod 71) ≠ 3 at h7
    change 71=11 → (15 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (59 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (16 : ZMod 71)
    change (16 : ZMod 71) ≠ 0 at hp
    change (16 : ZMod 71)-1 ≠ 0 at ha
    change (16 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 71)+1)) at hr
    change IsSquare (3-(16 : ZMod 71)) at hs
    change 71=7 → (16 : ZMod 71) ≠ 3 at h7
    change 71=11 → (16 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 71)
    change (17 : ZMod 71) ≠ 0 at hp
    change (17 : ZMod 71)-1 ≠ 0 at ha
    change (17 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 71)+1)) at hr
    change IsSquare (3-(17 : ZMod 71)) at hs
    change 71=7 → (17 : ZMod 71) ≠ 3 at h7
    change 71=11 → (17 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨17,![17,21,3,19],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (18 : ZMod 71)
    change (18 : ZMod 71) ≠ 0 at hp
    change (18 : ZMod 71)-1 ≠ 0 at ha
    change (18 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 71)+1)) at hr
    change IsSquare (3-(18 : ZMod 71)) at hs
    change 71=7 → (18 : ZMod 71) ≠ 3 at h7
    change 71=11 → (18 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (56 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (19 : ZMod 71)
    change (19 : ZMod 71) ≠ 0 at hp
    change (19 : ZMod 71)-1 ≠ 0 at ha
    change (19 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 71)+1)) at hr
    change IsSquare (3-(19 : ZMod 71)) at hs
    change 71=7 → (19 : ZMod 71) ≠ 3 at h7
    change 71=11 → (19 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (55 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (20 : ZMod 71)
    change (20 : ZMod 71) ≠ 0 at hp
    change (20 : ZMod 71)-1 ≠ 0 at ha
    change (20 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 71)+1)) at hr
    change IsSquare (3-(20 : ZMod 71)) at hs
    change 71=7 → (20 : ZMod 71) ≠ 3 at h7
    change 71=11 → (20 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (42 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (21 : ZMod 71)
    change (21 : ZMod 71) ≠ 0 at hp
    change (21 : ZMod 71)-1 ≠ 0 at ha
    change (21 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 71)+1)) at hr
    change IsSquare (3-(21 : ZMod 71)) at hs
    change 71=7 → (21 : ZMod 71) ≠ 3 at h7
    change 71=11 → (21 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (44 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (22 : ZMod 71)
    change (22 : ZMod 71) ≠ 0 at hp
    change (22 : ZMod 71)-1 ≠ 0 at ha
    change (22 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 71)+1)) at hr
    change IsSquare (3-(22 : ZMod 71)) at hs
    change 71=7 → (22 : ZMod 71) ≠ 3 at h7
    change 71=11 → (22 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (46 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (23 : ZMod 71)
    change (23 : ZMod 71) ≠ 0 at hp
    change (23 : ZMod 71)-1 ≠ 0 at ha
    change (23 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 71)+1)) at hr
    change IsSquare (3-(23 : ZMod 71)) at hs
    change 71=7 → (23 : ZMod 71) ≠ 3 at h7
    change 71=11 → (23 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (51 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (24 : ZMod 71)
    change (24 : ZMod 71) ≠ 0 at hp
    change (24 : ZMod 71)-1 ≠ 0 at ha
    change (24 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 71)+1)) at hr
    change IsSquare (3-(24 : ZMod 71)) at hs
    change 71=7 → (24 : ZMod 71) ≠ 3 at h7
    change 71=11 → (24 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,5,11,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (25 : ZMod 71)
    change (25 : ZMod 71) ≠ 0 at hp
    change (25 : ZMod 71)-1 ≠ 0 at ha
    change (25 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 71)+1)) at hr
    change IsSquare (3-(25 : ZMod 71)) at hs
    change 71=7 → (25 : ZMod 71) ≠ 3 at h7
    change 71=11 → (25 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (52 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (26 : ZMod 71)
    change (26 : ZMod 71) ≠ 0 at hp
    change (26 : ZMod 71)-1 ≠ 0 at ha
    change (26 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 71)+1)) at hr
    change IsSquare (3-(26 : ZMod 71)) at hs
    change 71=7 → (26 : ZMod 71) ≠ 3 at h7
    change 71=11 → (26 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨7,![18,4,19,29],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (27 : ZMod 71)
    change (27 : ZMod 71) ≠ 0 at hp
    change (27 : ZMod 71)-1 ≠ 0 at ha
    change (27 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 71)+1)) at hr
    change IsSquare (3-(27 : ZMod 71)) at hs
    change 71=7 → (27 : ZMod 71) ≠ 3 at h7
    change 71=11 → (27 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (56 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (28 : ZMod 71)
    change (28 : ZMod 71) ≠ 0 at hp
    change (28 : ZMod 71)-1 ≠ 0 at ha
    change (28 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 71)+1)) at hr
    change IsSquare (3-(28 : ZMod 71)) at hs
    change 71=7 → (28 : ZMod 71) ≠ 3 at h7
    change 71=11 → (28 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (46 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (29 : ZMod 71)
    change (29 : ZMod 71) ≠ 0 at hp
    change (29 : ZMod 71)-1 ≠ 0 at ha
    change (29 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 71)+1)) at hr
    change IsSquare (3-(29 : ZMod 71)) at hs
    change 71=7 → (29 : ZMod 71) ≠ 3 at h7
    change 71=11 → (29 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,21,29,32],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (30 : ZMod 71)
    change (30 : ZMod 71) ≠ 0 at hp
    change (30 : ZMod 71)-1 ≠ 0 at ha
    change (30 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 71)+1)) at hr
    change IsSquare (3-(30 : ZMod 71)) at hs
    change 71=7 → (30 : ZMod 71) ≠ 3 at h7
    change 71=11 → (30 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (62 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (31 : ZMod 71)
    change (31 : ZMod 71) ≠ 0 at hp
    change (31 : ZMod 71)-1 ≠ 0 at ha
    change (31 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 71)+1)) at hr
    change IsSquare (3-(31 : ZMod 71)) at hs
    change 71=7 → (31 : ZMod 71) ≠ 3 at h7
    change 71=11 → (31 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨7,![2,17,21,10],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (32 : ZMod 71)
    change (32 : ZMod 71) ≠ 0 at hp
    change (32 : ZMod 71)-1 ≠ 0 at ha
    change (32 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 71)+1)) at hr
    change IsSquare (3-(32 : ZMod 71)) at hs
    change 71=7 → (32 : ZMod 71) ≠ 3 at h7
    change 71=11 → (32 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (66 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (33 : ZMod 71)
    change (33 : ZMod 71) ≠ 0 at hp
    change (33 : ZMod 71)-1 ≠ 0 at ha
    change (33 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 71)+1)) at hr
    change IsSquare (3-(33 : ZMod 71)) at hs
    change 71=7 → (33 : ZMod 71) ≠ 3 at h7
    change 71=11 → (33 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (68 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (34 : ZMod 71)
    change (34 : ZMod 71) ≠ 0 at hp
    change (34 : ZMod 71)-1 ≠ 0 at ha
    change (34 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 71)+1)) at hr
    change IsSquare (3-(34 : ZMod 71)) at hs
    change 71=7 → (34 : ZMod 71) ≠ 3 at h7
    change 71=11 → (34 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (70 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (35 : ZMod 71)
    change (35 : ZMod 71) ≠ 0 at hp
    change (35 : ZMod 71)-1 ≠ 0 at ha
    change (35 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 71)+1)) at hr
    change IsSquare (3-(35 : ZMod 71)) at hs
    change 71=7 → (35 : ZMod 71) ≠ 3 at h7
    change 71=11 → (35 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (36 : ZMod 71)
    change (36 : ZMod 71) ≠ 0 at hp
    change (36 : ZMod 71)-1 ≠ 0 at ha
    change (36 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 71)+1)) at hr
    change IsSquare (3-(36 : ZMod 71)) at hs
    change 71=7 → (36 : ZMod 71) ≠ 3 at h7
    change 71=11 → (36 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,1,28,26],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (37 : ZMod 71)
    change (37 : ZMod 71) ≠ 0 at hp
    change (37 : ZMod 71)-1 ≠ 0 at ha
    change (37 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 71)+1)) at hr
    change IsSquare (3-(37 : ZMod 71)) at hs
    change 71=7 → (37 : ZMod 71) ≠ 3 at h7
    change 71=11 → (37 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![26,0,9,28],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (38 : ZMod 71)
    change (38 : ZMod 71) ≠ 0 at hp
    change (38 : ZMod 71)-1 ≠ 0 at ha
    change (38 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 71)+1)) at hr
    change IsSquare (3-(38 : ZMod 71)) at hs
    change 71=7 → (38 : ZMod 71) ≠ 3 at h7
    change 71=11 → (38 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (39 : ZMod 71)
    change (39 : ZMod 71) ≠ 0 at hp
    change (39 : ZMod 71)-1 ≠ 0 at ha
    change (39 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 71)+1)) at hr
    change IsSquare (3-(39 : ZMod 71)) at hs
    change 71=7 → (39 : ZMod 71) ≠ 3 at h7
    change 71=11 → (39 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (40 : ZMod 71)
    change (40 : ZMod 71) ≠ 0 at hp
    change (40 : ZMod 71)-1 ≠ 0 at ha
    change (40 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 71)+1)) at hr
    change IsSquare (3-(40 : ZMod 71)) at hs
    change 71=7 → (40 : ZMod 71) ≠ 3 at h7
    change 71=11 → (40 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (41 : ZMod 71)
    change (41 : ZMod 71) ≠ 0 at hp
    change (41 : ZMod 71)-1 ≠ 0 at ha
    change (41 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 71)+1)) at hr
    change IsSquare (3-(41 : ZMod 71)) at hs
    change 71=7 → (41 : ZMod 71) ≠ 3 at h7
    change 71=11 → (41 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (42 : ZMod 71)
    change (42 : ZMod 71) ≠ 0 at hp
    change (42 : ZMod 71)-1 ≠ 0 at ha
    change (42 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 71)+1)) at hr
    change IsSquare (3-(42 : ZMod 71)) at hs
    change 71=7 → (42 : ZMod 71) ≠ 3 at h7
    change 71=11 → (42 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,29,21,16],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (43 : ZMod 71)
    change (43 : ZMod 71) ≠ 0 at hp
    change (43 : ZMod 71)-1 ≠ 0 at ha
    change (43 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((43 : ZMod 71)+1)) at hr
    change IsSquare (3-(43 : ZMod 71)) at hs
    change 71=7 → (43 : ZMod 71) ≠ 3 at h7
    change 71=11 → (43 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (44 : ZMod 71)
    change (44 : ZMod 71) ≠ 0 at hp
    change (44 : ZMod 71)-1 ≠ 0 at ha
    change (44 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((44 : ZMod 71)+1)) at hr
    change IsSquare (3-(44 : ZMod 71)) at hs
    change 71=7 → (44 : ZMod 71) ≠ 3 at h7
    change 71=11 → (44 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨26,![24,34,4,13],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (45 : ZMod 71)
    change (45 : ZMod 71) ≠ 0 at hp
    change (45 : ZMod 71)-1 ≠ 0 at ha
    change (45 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((45 : ZMod 71)+1)) at hr
    change IsSquare (3-(45 : ZMod 71)) at hs
    change 71=7 → (45 : ZMod 71) ≠ 3 at h7
    change 71=11 → (45 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (46 : ZMod 71)
    change (46 : ZMod 71) ≠ 0 at hp
    change (46 : ZMod 71)-1 ≠ 0 at ha
    change (46 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((46 : ZMod 71)+1)) at hr
    change IsSquare (3-(46 : ZMod 71)) at hs
    change 71=7 → (46 : ZMod 71) ≠ 3 at h7
    change 71=11 → (46 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (47 : ZMod 71)
    change (47 : ZMod 71) ≠ 0 at hp
    change (47 : ZMod 71)-1 ≠ 0 at ha
    change (47 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((47 : ZMod 71)+1)) at hr
    change IsSquare (3-(47 : ZMod 71)) at hs
    change 71=7 → (47 : ZMod 71) ≠ 3 at h7
    change 71=11 → (47 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,11,5,30],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (48 : ZMod 71)
    change (48 : ZMod 71) ≠ 0 at hp
    change (48 : ZMod 71)-1 ≠ 0 at ha
    change (48 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((48 : ZMod 71)+1)) at hr
    change IsSquare (3-(48 : ZMod 71)) at hs
    change 71=7 → (48 : ZMod 71) ≠ 3 at h7
    change 71=11 → (48 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (49 : ZMod 71)
    change (49 : ZMod 71) ≠ 0 at hp
    change (49 : ZMod 71)-1 ≠ 0 at ha
    change (49 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((49 : ZMod 71)+1)) at hr
    change IsSquare (3-(49 : ZMod 71)) at hs
    change 71=7 → (49 : ZMod 71) ≠ 3 at h7
    change 71=11 → (49 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![7,0,22,13],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (50 : ZMod 71)
    change (50 : ZMod 71) ≠ 0 at hp
    change (50 : ZMod 71)-1 ≠ 0 at ha
    change (50 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((50 : ZMod 71)+1)) at hr
    change IsSquare (3-(50 : ZMod 71)) at hs
    change 71=7 → (50 : ZMod 71) ≠ 3 at h7
    change 71=11 → (50 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (51 : ZMod 71)
    change (51 : ZMod 71) ≠ 0 at hp
    change (51 : ZMod 71)-1 ≠ 0 at ha
    change (51 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((51 : ZMod 71)+1)) at hr
    change IsSquare (3-(51 : ZMod 71)) at hs
    change 71=7 → (51 : ZMod 71) ≠ 3 at h7
    change 71=11 → (51 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (52 : ZMod 71)
    change (52 : ZMod 71) ≠ 0 at hp
    change (52 : ZMod 71)-1 ≠ 0 at ha
    change (52 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((52 : ZMod 71)+1)) at hr
    change IsSquare (3-(52 : ZMod 71)) at hs
    change 71=7 → (52 : ZMod 71) ≠ 3 at h7
    change 71=11 → (52 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (53 : ZMod 71)
    change (53 : ZMod 71) ≠ 0 at hp
    change (53 : ZMod 71)-1 ≠ 0 at ha
    change (53 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((53 : ZMod 71)+1)) at hr
    change IsSquare (3-(53 : ZMod 71)) at hs
    change 71=7 → (53 : ZMod 71) ≠ 3 at h7
    change 71=11 → (53 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (54 : ZMod 71)
    change (54 : ZMod 71) ≠ 0 at hp
    change (54 : ZMod 71)-1 ≠ 0 at ha
    change (54 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((54 : ZMod 71)+1)) at hr
    change IsSquare (3-(54 : ZMod 71)) at hs
    change 71=7 → (54 : ZMod 71) ≠ 3 at h7
    change 71=11 → (54 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (55 : ZMod 71)
    change (55 : ZMod 71) ≠ 0 at hp
    change (55 : ZMod 71)-1 ≠ 0 at ha
    change (55 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((55 : ZMod 71)+1)) at hr
    change IsSquare (3-(55 : ZMod 71)) at hs
    change 71=7 → (55 : ZMod 71) ≠ 3 at h7
    change 71=11 → (55 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (41 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (56 : ZMod 71)
    change (56 : ZMod 71) ≠ 0 at hp
    change (56 : ZMod 71)-1 ≠ 0 at ha
    change (56 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((56 : ZMod 71)+1)) at hr
    change IsSquare (3-(56 : ZMod 71)) at hs
    change 71=7 → (56 : ZMod 71) ≠ 3 at h7
    change 71=11 → (56 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,23,16,25],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (57 : ZMod 71)
    change (57 : ZMod 71) ≠ 0 at hp
    change (57 : ZMod 71)-1 ≠ 0 at ha
    change (57 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((57 : ZMod 71)+1)) at hr
    change IsSquare (3-(57 : ZMod 71)) at hs
    change 71=7 → (57 : ZMod 71) ≠ 3 at h7
    change 71=11 → (57 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (58 : ZMod 71)
    change (58 : ZMod 71) ≠ 0 at hp
    change (58 : ZMod 71)-1 ≠ 0 at ha
    change (58 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((58 : ZMod 71)+1)) at hr
    change IsSquare (3-(58 : ZMod 71)) at hs
    change 71=7 → (58 : ZMod 71) ≠ 3 at h7
    change 71=11 → (58 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (47 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (59 : ZMod 71)
    change (59 : ZMod 71) ≠ 0 at hp
    change (59 : ZMod 71)-1 ≠ 0 at ha
    change (59 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((59 : ZMod 71)+1)) at hr
    change IsSquare (3-(59 : ZMod 71)) at hs
    change 71=7 → (59 : ZMod 71) ≠ 3 at h7
    change 71=11 → (59 : ZMod 71) ≠ 5 at h11
    apply Or.inl
    refine ⟨7,![22,25,26,18],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (60 : ZMod 71)
    change (60 : ZMod 71) ≠ 0 at hp
    change (60 : ZMod 71)-1 ≠ 0 at ha
    change (60 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((60 : ZMod 71)+1)) at hr
    change IsSquare (3-(60 : ZMod 71)) at hs
    change 71=7 → (60 : ZMod 71) ≠ 3 at h7
    change 71=11 → (60 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (51 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (61 : ZMod 71)
    change (61 : ZMod 71) ≠ 0 at hp
    change (61 : ZMod 71)-1 ≠ 0 at ha
    change (61 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((61 : ZMod 71)+1)) at hr
    change IsSquare (3-(61 : ZMod 71)) at hs
    change 71=7 → (61 : ZMod 71) ≠ 3 at h7
    change 71=11 → (61 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (53 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (62 : ZMod 71)
    change (62 : ZMod 71) ≠ 0 at hp
    change (62 : ZMod 71)-1 ≠ 0 at ha
    change (62 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((62 : ZMod 71)+1)) at hr
    change IsSquare (3-(62 : ZMod 71)) at hs
    change 71=7 → (62 : ZMod 71) ≠ 3 at h7
    change 71=11 → (62 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (55 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (63 : ZMod 71)
    change (63 : ZMod 71) ≠ 0 at hp
    change (63 : ZMod 71)-1 ≠ 0 at ha
    change (63 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((63 : ZMod 71)+1)) at hr
    change IsSquare (3-(63 : ZMod 71)) at hs
    change 71=7 → (63 : ZMod 71) ≠ 3 at h7
    change 71=11 → (63 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (64 : ZMod 71)
    change (64 : ZMod 71) ≠ 0 at hp
    change (64 : ZMod 71)-1 ≠ 0 at ha
    change (64 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((64 : ZMod 71)+1)) at hr
    change IsSquare (3-(64 : ZMod 71)) at hs
    change 71=7 → (64 : ZMod 71) ≠ 3 at h7
    change 71=11 → (64 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (59 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (65 : ZMod 71)
    change (65 : ZMod 71) ≠ 0 at hp
    change (65 : ZMod 71)-1 ≠ 0 at ha
    change (65 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((65 : ZMod 71)+1)) at hr
    change IsSquare (3-(65 : ZMod 71)) at hs
    change 71=7 → (65 : ZMod 71) ≠ 3 at h7
    change 71=11 → (65 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (61 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (66 : ZMod 71)
    change (66 : ZMod 71) ≠ 0 at hp
    change (66 : ZMod 71)-1 ≠ 0 at ha
    change (66 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((66 : ZMod 71)+1)) at hr
    change IsSquare (3-(66 : ZMod 71)) at hs
    change 71=7 → (66 : ZMod 71) ≠ 3 at h7
    change 71=11 → (66 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (63 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (67 : ZMod 71)
    change (67 : ZMod 71) ≠ 0 at hp
    change (67 : ZMod 71)-1 ≠ 0 at ha
    change (67 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((67 : ZMod 71)+1)) at hr
    change IsSquare (3-(67 : ZMod 71)) at hs
    change 71=7 → (67 : ZMod 71) ≠ 3 at h7
    change 71=11 → (67 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (65 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (68 : ZMod 71)
    change (68 : ZMod 71) ≠ 0 at hp
    change (68 : ZMod 71)-1 ≠ 0 at ha
    change (68 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((68 : ZMod 71)+1)) at hr
    change IsSquare (3-(68 : ZMod 71)) at hs
    change 71=7 → (68 : ZMod 71) ≠ 3 at h7
    change 71=11 → (68 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (67 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (69 : ZMod 71)
    change (69 : ZMod 71) ≠ 0 at hp
    change (69 : ZMod 71)-1 ≠ 0 at ha
    change (69 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((69 : ZMod 71)+1)) at hr
    change IsSquare (3-(69 : ZMod 71)) at hs
    change 71=7 → (69 : ZMod 71) ≠ 3 at h7
    change 71=11 → (69 : ZMod 71) ≠ 5 at h11
    have hn : ¬IsSquare (69 : ZMod 71) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (70 : ZMod 71)
    change (70 : ZMod 71) ≠ 0 at hp
    change (70 : ZMod 71)-1 ≠ 0 at ha
    change (70 : ZMod 71)+1 ≠ 0 at hb
    change IsSquare (2*((70 : ZMod 71)+1)) at hr
    change IsSquare (3-(70 : ZMod 71)) at hs
    change 71=7 → (70 : ZMod 71) ≠ 3 at h7
    change 71=11 → (70 : ZMod 71) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts71

private instance prime73 : Fact (Nat.Prime 73) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts73 (p : ZMod 73) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 73=7 → p ≠ 3) (h11 : 73=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 73)
    change (0 : ZMod 73) ≠ 0 at hp
    change (0 : ZMod 73)-1 ≠ 0 at ha
    change (0 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 73)+1)) at hr
    change IsSquare (3-(0 : ZMod 73)) at hs
    change 73=7 → (0 : ZMod 73) ≠ 3 at h7
    change 73=11 → (0 : ZMod 73) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 73)
    change (1 : ZMod 73) ≠ 0 at hp
    change (1 : ZMod 73)-1 ≠ 0 at ha
    change (1 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 73)+1)) at hr
    change IsSquare (3-(1 : ZMod 73)) at hs
    change 73=7 → (1 : ZMod 73) ≠ 3 at h7
    change 73=11 → (1 : ZMod 73) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 73)
    change (2 : ZMod 73) ≠ 0 at hp
    change (2 : ZMod 73)-1 ≠ 0 at ha
    change (2 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 73)+1)) at hr
    change IsSquare (3-(2 : ZMod 73)) at hs
    change 73=7 → (2 : ZMod 73) ≠ 3 at h7
    change 73=11 → (2 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,12,15,21],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (3 : ZMod 73)
    change (3 : ZMod 73) ≠ 0 at hp
    change (3 : ZMod 73)-1 ≠ 0 at ha
    change (3 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 73)+1)) at hr
    change IsSquare (3-(3 : ZMod 73)) at hs
    change 73=7 → (3 : ZMod 73) ≠ 3 at h7
    change 73=11 → (3 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,19,9,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (4 : ZMod 73)
    change (4 : ZMod 73) ≠ 0 at hp
    change (4 : ZMod 73)-1 ≠ 0 at ha
    change (4 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 73)+1)) at hr
    change IsSquare (3-(4 : ZMod 73)) at hs
    change 73=7 → (4 : ZMod 73) ≠ 3 at h7
    change 73=11 → (4 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (5 : ZMod 73)
    change (5 : ZMod 73) ≠ 0 at hp
    change (5 : ZMod 73)-1 ≠ 0 at ha
    change (5 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 73)+1)) at hr
    change IsSquare (3-(5 : ZMod 73)) at hs
    change 73=7 → (5 : ZMod 73) ≠ 3 at h7
    change 73=11 → (5 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,24,31,15],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (6 : ZMod 73)
    change (6 : ZMod 73) ≠ 0 at hp
    change (6 : ZMod 73)-1 ≠ 0 at ha
    change (6 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 73)+1)) at hr
    change IsSquare (3-(6 : ZMod 73)) at hs
    change 73=7 → (6 : ZMod 73) ≠ 3 at h7
    change 73=11 → (6 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 73)
    change (7 : ZMod 73) ≠ 0 at hp
    change (7 : ZMod 73)-1 ≠ 0 at ha
    change (7 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 73)+1)) at hr
    change IsSquare (3-(7 : ZMod 73)) at hs
    change 73=7 → (7 : ZMod 73) ≠ 3 at h7
    change 73=11 → (7 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,34,4,9],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (8 : ZMod 73)
    change (8 : ZMod 73) ≠ 0 at hp
    change (8 : ZMod 73)-1 ≠ 0 at ha
    change (8 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 73)+1)) at hr
    change IsSquare (3-(8 : ZMod 73)) at hs
    change 73=7 → (8 : ZMod 73) ≠ 3 at h7
    change 73=11 → (8 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (68 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (9 : ZMod 73)
    change (9 : ZMod 73) ≠ 0 at hp
    change (9 : ZMod 73)-1 ≠ 0 at ha
    change (9 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 73)+1)) at hr
    change IsSquare (3-(9 : ZMod 73)) at hs
    change 73=7 → (9 : ZMod 73) ≠ 3 at h7
    change 73=11 → (9 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (10 : ZMod 73)
    change (10 : ZMod 73) ≠ 0 at hp
    change (10 : ZMod 73)-1 ≠ 0 at ha
    change (10 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 73)+1)) at hr
    change IsSquare (3-(10 : ZMod 73)) at hs
    change 73=7 → (10 : ZMod 73) ≠ 3 at h7
    change 73=11 → (10 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 73)
    change (11 : ZMod 73) ≠ 0 at hp
    change (11 : ZMod 73)-1 ≠ 0 at ha
    change (11 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 73)+1)) at hr
    change IsSquare (3-(11 : ZMod 73)) at hs
    change 73=7 → (11 : ZMod 73) ≠ 3 at h7
    change 73=11 → (11 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨11,![11,28,19,7],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (12 : ZMod 73)
    change (12 : ZMod 73) ≠ 0 at hp
    change (12 : ZMod 73)-1 ≠ 0 at ha
    change (12 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 73)+1)) at hr
    change IsSquare (3-(12 : ZMod 73)) at hs
    change 73=7 → (12 : ZMod 73) ≠ 3 at h7
    change 73=11 → (12 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (13 : ZMod 73)
    change (13 : ZMod 73) ≠ 0 at hp
    change (13 : ZMod 73)-1 ≠ 0 at ha
    change (13 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 73)+1)) at hr
    change IsSquare (3-(13 : ZMod 73)) at hs
    change 73=7 → (13 : ZMod 73) ≠ 3 at h7
    change 73=11 → (13 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (14 : ZMod 73)
    change (14 : ZMod 73) ≠ 0 at hp
    change (14 : ZMod 73)-1 ≠ 0 at ha
    change (14 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 73)+1)) at hr
    change IsSquare (3-(14 : ZMod 73)) at hs
    change 73=7 → (14 : ZMod 73) ≠ 3 at h7
    change 73=11 → (14 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 73)
    change (15 : ZMod 73) ≠ 0 at hp
    change (15 : ZMod 73)-1 ≠ 0 at ha
    change (15 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 73)+1)) at hr
    change IsSquare (3-(15 : ZMod 73)) at hs
    change 73=7 → (15 : ZMod 73) ≠ 3 at h7
    change 73=11 → (15 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨11,![26,34,26,30],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (16 : ZMod 73)
    change (16 : ZMod 73) ≠ 0 at hp
    change (16 : ZMod 73)-1 ≠ 0 at ha
    change (16 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 73)+1)) at hr
    change IsSquare (3-(16 : ZMod 73)) at hs
    change 73=7 → (16 : ZMod 73) ≠ 3 at h7
    change 73=11 → (16 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 73)
    change (17 : ZMod 73) ≠ 0 at hp
    change (17 : ZMod 73)-1 ≠ 0 at ha
    change (17 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 73)+1)) at hr
    change IsSquare (3-(17 : ZMod 73)) at hs
    change 73=7 → (17 : ZMod 73) ≠ 3 at h7
    change 73=11 → (17 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (59 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (18 : ZMod 73)
    change (18 : ZMod 73) ≠ 0 at hp
    change (18 : ZMod 73)-1 ≠ 0 at ha
    change (18 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 73)+1)) at hr
    change IsSquare (3-(18 : ZMod 73)) at hs
    change 73=7 → (18 : ZMod 73) ≠ 3 at h7
    change 73=11 → (18 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (58 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (19 : ZMod 73)
    change (19 : ZMod 73) ≠ 0 at hp
    change (19 : ZMod 73)-1 ≠ 0 at ha
    change (19 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 73)+1)) at hr
    change IsSquare (3-(19 : ZMod 73)) at hs
    change 73=7 → (19 : ZMod 73) ≠ 3 at h7
    change 73=11 → (19 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (40 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (20 : ZMod 73)
    change (20 : ZMod 73) ≠ 0 at hp
    change (20 : ZMod 73)-1 ≠ 0 at ha
    change (20 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 73)+1)) at hr
    change IsSquare (3-(20 : ZMod 73)) at hs
    change 73=7 → (20 : ZMod 73) ≠ 3 at h7
    change 73=11 → (20 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (42 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (21 : ZMod 73)
    change (21 : ZMod 73) ≠ 0 at hp
    change (21 : ZMod 73)-1 ≠ 0 at ha
    change (21 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 73)+1)) at hr
    change IsSquare (3-(21 : ZMod 73)) at hs
    change 73=7 → (21 : ZMod 73) ≠ 3 at h7
    change 73=11 → (21 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (44 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (22 : ZMod 73)
    change (22 : ZMod 73) ≠ 0 at hp
    change (22 : ZMod 73)-1 ≠ 0 at ha
    change (22 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 73)+1)) at hr
    change IsSquare (3-(22 : ZMod 73)) at hs
    change 73=7 → (22 : ZMod 73) ≠ 3 at h7
    change 73=11 → (22 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨11,![13,36,25,20],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (23 : ZMod 73)
    change (23 : ZMod 73) ≠ 0 at hp
    change (23 : ZMod 73)-1 ≠ 0 at ha
    change (23 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 73)+1)) at hr
    change IsSquare (3-(23 : ZMod 73)) at hs
    change 73=7 → (23 : ZMod 73) ≠ 3 at h7
    change 73=11 → (23 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (53 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (24 : ZMod 73)
    change (24 : ZMod 73) ≠ 0 at hp
    change (24 : ZMod 73)-1 ≠ 0 at ha
    change (24 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 73)+1)) at hr
    change IsSquare (3-(24 : ZMod 73)) at hs
    change 73=7 → (24 : ZMod 73) ≠ 3 at h7
    change 73=11 → (24 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (52 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (25 : ZMod 73)
    change (25 : ZMod 73) ≠ 0 at hp
    change (25 : ZMod 73)-1 ≠ 0 at ha
    change (25 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 73)+1)) at hr
    change IsSquare (3-(25 : ZMod 73)) at hs
    change 73=7 → (25 : ZMod 73) ≠ 3 at h7
    change 73=11 → (25 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (52 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (26 : ZMod 73)
    change (26 : ZMod 73) ≠ 0 at hp
    change (26 : ZMod 73)-1 ≠ 0 at ha
    change (26 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 73)+1)) at hr
    change IsSquare (3-(26 : ZMod 73)) at hs
    change 73=7 → (26 : ZMod 73) ≠ 3 at h7
    change 73=11 → (26 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,13,28,10],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (27 : ZMod 73)
    change (27 : ZMod 73) ≠ 0 at hp
    change (27 : ZMod 73)-1 ≠ 0 at ha
    change (27 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 73)+1)) at hr
    change IsSquare (3-(27 : ZMod 73)) at hs
    change 73=7 → (27 : ZMod 73) ≠ 3 at h7
    change 73=11 → (27 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (56 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (28 : ZMod 73)
    change (28 : ZMod 73) ≠ 0 at hp
    change (28 : ZMod 73)-1 ≠ 0 at ha
    change (28 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 73)+1)) at hr
    change IsSquare (3-(28 : ZMod 73)) at hs
    change 73=7 → (28 : ZMod 73) ≠ 3 at h7
    change 73=11 → (28 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (58 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (29 : ZMod 73)
    change (29 : ZMod 73) ≠ 0 at hp
    change (29 : ZMod 73)-1 ≠ 0 at ha
    change (29 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 73)+1)) at hr
    change IsSquare (3-(29 : ZMod 73)) at hs
    change 73=7 → (29 : ZMod 73) ≠ 3 at h7
    change 73=11 → (29 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (60 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (30 : ZMod 73)
    change (30 : ZMod 73) ≠ 0 at hp
    change (30 : ZMod 73)-1 ≠ 0 at ha
    change (30 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 73)+1)) at hr
    change IsSquare (3-(30 : ZMod 73)) at hs
    change 73=7 → (30 : ZMod 73) ≠ 3 at h7
    change 73=11 → (30 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (62 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (31 : ZMod 73)
    change (31 : ZMod 73) ≠ 0 at hp
    change (31 : ZMod 73)-1 ≠ 0 at ha
    change (31 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 73)+1)) at hr
    change IsSquare (3-(31 : ZMod 73)) at hs
    change 73=7 → (31 : ZMod 73) ≠ 3 at h7
    change 73=11 → (31 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (45 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (32 : ZMod 73)
    change (32 : ZMod 73) ≠ 0 at hp
    change (32 : ZMod 73)-1 ≠ 0 at ha
    change (32 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 73)+1)) at hr
    change IsSquare (3-(32 : ZMod 73)) at hs
    change 73=7 → (32 : ZMod 73) ≠ 3 at h7
    change 73=11 → (32 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (66 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (33 : ZMod 73)
    change (33 : ZMod 73) ≠ 0 at hp
    change (33 : ZMod 73)-1 ≠ 0 at ha
    change (33 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 73)+1)) at hr
    change IsSquare (3-(33 : ZMod 73)) at hs
    change 73=7 → (33 : ZMod 73) ≠ 3 at h7
    change 73=11 → (33 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (68 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (34 : ZMod 73)
    change (34 : ZMod 73) ≠ 0 at hp
    change (34 : ZMod 73)-1 ≠ 0 at ha
    change (34 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 73)+1)) at hr
    change IsSquare (3-(34 : ZMod 73)) at hs
    change 73=7 → (34 : ZMod 73) ≠ 3 at h7
    change 73=11 → (34 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (42 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (35 : ZMod 73)
    change (35 : ZMod 73) ≠ 0 at hp
    change (35 : ZMod 73)-1 ≠ 0 at ha
    change (35 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 73)+1)) at hr
    change IsSquare (3-(35 : ZMod 73)) at hs
    change 73=7 → (35 : ZMod 73) ≠ 3 at h7
    change 73=11 → (35 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![20,0,12,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (36 : ZMod 73)
    change (36 : ZMod 73) ≠ 0 at hp
    change (36 : ZMod 73)-1 ≠ 0 at ha
    change (36 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 73)+1)) at hr
    change IsSquare (3-(36 : ZMod 73)) at hs
    change 73=7 → (36 : ZMod 73) ≠ 3 at h7
    change 73=11 → (36 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (40 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (37 : ZMod 73)
    change (37 : ZMod 73) ≠ 0 at hp
    change (37 : ZMod 73)-1 ≠ 0 at ha
    change (37 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 73)+1)) at hr
    change IsSquare (3-(37 : ZMod 73)) at hs
    change 73=7 → (37 : ZMod 73) ≠ 3 at h7
    change 73=11 → (37 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (38 : ZMod 73)
    change (38 : ZMod 73) ≠ 0 at hp
    change (38 : ZMod 73)-1 ≠ 0 at ha
    change (38 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 73)+1)) at hr
    change IsSquare (3-(38 : ZMod 73)) at hs
    change 73=7 → (38 : ZMod 73) ≠ 3 at h7
    change 73=11 → (38 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (39 : ZMod 73)
    change (39 : ZMod 73) ≠ 0 at hp
    change (39 : ZMod 73)-1 ≠ 0 at ha
    change (39 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 73)+1)) at hr
    change IsSquare (3-(39 : ZMod 73)) at hs
    change 73=7 → (39 : ZMod 73) ≠ 3 at h7
    change 73=11 → (39 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (40 : ZMod 73)
    change (40 : ZMod 73) ≠ 0 at hp
    change (40 : ZMod 73)-1 ≠ 0 at ha
    change (40 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 73)+1)) at hr
    change IsSquare (3-(40 : ZMod 73)) at hs
    change 73=7 → (40 : ZMod 73) ≠ 3 at h7
    change 73=11 → (40 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨11,![32,14,20,18],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (41 : ZMod 73)
    change (41 : ZMod 73) ≠ 0 at hp
    change (41 : ZMod 73)-1 ≠ 0 at ha
    change (41 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 73)+1)) at hr
    change IsSquare (3-(41 : ZMod 73)) at hs
    change 73=7 → (41 : ZMod 73) ≠ 3 at h7
    change 73=11 → (41 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (11 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (42 : ZMod 73)
    change (42 : ZMod 73) ≠ 0 at hp
    change (42 : ZMod 73)-1 ≠ 0 at ha
    change (42 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 73)+1)) at hr
    change IsSquare (3-(42 : ZMod 73)) at hs
    change 73=7 → (42 : ZMod 73) ≠ 3 at h7
    change 73=11 → (42 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (43 : ZMod 73)
    change (43 : ZMod 73) ≠ 0 at hp
    change (43 : ZMod 73)-1 ≠ 0 at ha
    change (43 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((43 : ZMod 73)+1)) at hr
    change IsSquare (3-(43 : ZMod 73)) at hs
    change 73=7 → (43 : ZMod 73) ≠ 3 at h7
    change 73=11 → (43 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (44 : ZMod 73)
    change (44 : ZMod 73) ≠ 0 at hp
    change (44 : ZMod 73)-1 ≠ 0 at ha
    change (44 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((44 : ZMod 73)+1)) at hr
    change IsSquare (3-(44 : ZMod 73)) at hs
    change 73=7 → (44 : ZMod 73) ≠ 3 at h7
    change 73=11 → (44 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (45 : ZMod 73)
    change (45 : ZMod 73) ≠ 0 at hp
    change (45 : ZMod 73)-1 ≠ 0 at ha
    change (45 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((45 : ZMod 73)+1)) at hr
    change IsSquare (3-(45 : ZMod 73)) at hs
    change 73=7 → (45 : ZMod 73) ≠ 3 at h7
    change 73=11 → (45 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (46 : ZMod 73)
    change (46 : ZMod 73) ≠ 0 at hp
    change (46 : ZMod 73)-1 ≠ 0 at ha
    change (46 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((46 : ZMod 73)+1)) at hr
    change IsSquare (3-(46 : ZMod 73)) at hs
    change 73=7 → (46 : ZMod 73) ≠ 3 at h7
    change 73=11 → (46 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (47 : ZMod 73)
    change (47 : ZMod 73) ≠ 0 at hp
    change (47 : ZMod 73)-1 ≠ 0 at ha
    change (47 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((47 : ZMod 73)+1)) at hr
    change IsSquare (3-(47 : ZMod 73)) at hs
    change 73=7 → (47 : ZMod 73) ≠ 3 at h7
    change 73=11 → (47 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (48 : ZMod 73)
    change (48 : ZMod 73) ≠ 0 at hp
    change (48 : ZMod 73)-1 ≠ 0 at ha
    change (48 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((48 : ZMod 73)+1)) at hr
    change IsSquare (3-(48 : ZMod 73)) at hs
    change 73=7 → (48 : ZMod 73) ≠ 3 at h7
    change 73=11 → (48 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (49 : ZMod 73)
    change (49 : ZMod 73) ≠ 0 at hp
    change (49 : ZMod 73)-1 ≠ 0 at ha
    change (49 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((49 : ZMod 73)+1)) at hr
    change IsSquare (3-(49 : ZMod 73)) at hs
    change 73=7 → (49 : ZMod 73) ≠ 3 at h7
    change 73=11 → (49 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,14,10,14],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (50 : ZMod 73)
    change (50 : ZMod 73) ≠ 0 at hp
    change (50 : ZMod 73)-1 ≠ 0 at ha
    change (50 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((50 : ZMod 73)+1)) at hr
    change IsSquare (3-(50 : ZMod 73)) at hs
    change 73=7 → (50 : ZMod 73) ≠ 3 at h7
    change 73=11 → (50 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (51 : ZMod 73)
    change (51 : ZMod 73) ≠ 0 at hp
    change (51 : ZMod 73)-1 ≠ 0 at ha
    change (51 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((51 : ZMod 73)+1)) at hr
    change IsSquare (3-(51 : ZMod 73)) at hs
    change 73=7 → (51 : ZMod 73) ≠ 3 at h7
    change 73=11 → (51 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (52 : ZMod 73)
    change (52 : ZMod 73) ≠ 0 at hp
    change (52 : ZMod 73)-1 ≠ 0 at ha
    change (52 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((52 : ZMod 73)+1)) at hr
    change IsSquare (3-(52 : ZMod 73)) at hs
    change 73=7 → (52 : ZMod 73) ≠ 3 at h7
    change 73=11 → (52 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (53 : ZMod 73)
    change (53 : ZMod 73) ≠ 0 at hp
    change (53 : ZMod 73)-1 ≠ 0 at ha
    change (53 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((53 : ZMod 73)+1)) at hr
    change IsSquare (3-(53 : ZMod 73)) at hs
    change 73=7 → (53 : ZMod 73) ≠ 3 at h7
    change 73=11 → (53 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨34,![14,1,35,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (54 : ZMod 73)
    change (54 : ZMod 73) ≠ 0 at hp
    change (54 : ZMod 73)-1 ≠ 0 at ha
    change (54 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((54 : ZMod 73)+1)) at hr
    change IsSquare (3-(54 : ZMod 73)) at hs
    change 73=7 → (54 : ZMod 73) ≠ 3 at h7
    change 73=11 → (54 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (55 : ZMod 73)
    change (55 : ZMod 73) ≠ 0 at hp
    change (55 : ZMod 73)-1 ≠ 0 at ha
    change (55 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((55 : ZMod 73)+1)) at hr
    change IsSquare (3-(55 : ZMod 73)) at hs
    change 73=7 → (55 : ZMod 73) ≠ 3 at h7
    change 73=11 → (55 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (56 : ZMod 73)
    change (56 : ZMod 73) ≠ 0 at hp
    change (56 : ZMod 73)-1 ≠ 0 at ha
    change (56 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((56 : ZMod 73)+1)) at hr
    change IsSquare (3-(56 : ZMod 73)) at hs
    change 73=7 → (56 : ZMod 73) ≠ 3 at h7
    change 73=11 → (56 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (57 : ZMod 73)
    change (57 : ZMod 73) ≠ 0 at hp
    change (57 : ZMod 73)-1 ≠ 0 at ha
    change (57 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((57 : ZMod 73)+1)) at hr
    change IsSquare (3-(57 : ZMod 73)) at hs
    change 73=7 → (57 : ZMod 73) ≠ 3 at h7
    change 73=11 → (57 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (58 : ZMod 73)
    change (58 : ZMod 73) ≠ 0 at hp
    change (58 : ZMod 73)-1 ≠ 0 at ha
    change (58 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((58 : ZMod 73)+1)) at hr
    change IsSquare (3-(58 : ZMod 73)) at hs
    change 73=7 → (58 : ZMod 73) ≠ 3 at h7
    change 73=11 → (58 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (45 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (59 : ZMod 73)
    change (59 : ZMod 73) ≠ 0 at hp
    change (59 : ZMod 73)-1 ≠ 0 at ha
    change (59 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((59 : ZMod 73)+1)) at hr
    change IsSquare (3-(59 : ZMod 73)) at hs
    change 73=7 → (59 : ZMod 73) ≠ 3 at h7
    change 73=11 → (59 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (47 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (60 : ZMod 73)
    change (60 : ZMod 73) ≠ 0 at hp
    change (60 : ZMod 73)-1 ≠ 0 at ha
    change (60 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((60 : ZMod 73)+1)) at hr
    change IsSquare (3-(60 : ZMod 73)) at hs
    change 73=7 → (60 : ZMod 73) ≠ 3 at h7
    change 73=11 → (60 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![30,22,28,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (61 : ZMod 73)
    change (61 : ZMod 73) ≠ 0 at hp
    change (61 : ZMod 73)-1 ≠ 0 at ha
    change (61 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((61 : ZMod 73)+1)) at hr
    change IsSquare (3-(61 : ZMod 73)) at hs
    change 73=7 → (61 : ZMod 73) ≠ 3 at h7
    change 73=11 → (61 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (51 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (62 : ZMod 73)
    change (62 : ZMod 73) ≠ 0 at hp
    change (62 : ZMod 73)-1 ≠ 0 at ha
    change (62 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((62 : ZMod 73)+1)) at hr
    change IsSquare (3-(62 : ZMod 73)) at hs
    change 73=7 → (62 : ZMod 73) ≠ 3 at h7
    change 73=11 → (62 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (53 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (63 : ZMod 73)
    change (63 : ZMod 73) ≠ 0 at hp
    change (63 : ZMod 73)-1 ≠ 0 at ha
    change (63 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((63 : ZMod 73)+1)) at hr
    change IsSquare (3-(63 : ZMod 73)) at hs
    change 73=7 → (63 : ZMod 73) ≠ 3 at h7
    change 73=11 → (63 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (64 : ZMod 73)
    change (64 : ZMod 73) ≠ 0 at hp
    change (64 : ZMod 73)-1 ≠ 0 at ha
    change (64 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((64 : ZMod 73)+1)) at hr
    change IsSquare (3-(64 : ZMod 73)) at hs
    change 73=7 → (64 : ZMod 73) ≠ 3 at h7
    change 73=11 → (64 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![8,0,25,36],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (65 : ZMod 73)
    change (65 : ZMod 73) ≠ 0 at hp
    change (65 : ZMod 73)-1 ≠ 0 at ha
    change (65 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((65 : ZMod 73)+1)) at hr
    change IsSquare (3-(65 : ZMod 73)) at hs
    change 73=7 → (65 : ZMod 73) ≠ 3 at h7
    change 73=11 → (65 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (59 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (66 : ZMod 73)
    change (66 : ZMod 73) ≠ 0 at hp
    change (66 : ZMod 73)-1 ≠ 0 at ha
    change (66 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((66 : ZMod 73)+1)) at hr
    change IsSquare (3-(66 : ZMod 73)) at hs
    change 73=7 → (66 : ZMod 73) ≠ 3 at h7
    change 73=11 → (66 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (67 : ZMod 73)
    change (67 : ZMod 73) ≠ 0 at hp
    change (67 : ZMod 73)-1 ≠ 0 at ha
    change (67 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((67 : ZMod 73)+1)) at hr
    change IsSquare (3-(67 : ZMod 73)) at hs
    change 73=7 → (67 : ZMod 73) ≠ 3 at h7
    change 73=11 → (67 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (63 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (68 : ZMod 73)
    change (68 : ZMod 73) ≠ 0 at hp
    change (68 : ZMod 73)-1 ≠ 0 at ha
    change (68 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((68 : ZMod 73)+1)) at hr
    change IsSquare (3-(68 : ZMod 73)) at hs
    change 73=7 → (68 : ZMod 73) ≠ 3 at h7
    change 73=11 → (68 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,31,24,19],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (69 : ZMod 73)
    change (69 : ZMod 73) ≠ 0 at hp
    change (69 : ZMod 73)-1 ≠ 0 at ha
    change (69 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((69 : ZMod 73)+1)) at hr
    change IsSquare (3-(69 : ZMod 73)) at hs
    change 73=7 → (69 : ZMod 73) ≠ 3 at h7
    change 73=11 → (69 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (70 : ZMod 73)
    change (70 : ZMod 73) ≠ 0 at hp
    change (70 : ZMod 73)-1 ≠ 0 at ha
    change (70 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((70 : ZMod 73)+1)) at hr
    change IsSquare (3-(70 : ZMod 73)) at hs
    change 73=7 → (70 : ZMod 73) ≠ 3 at h7
    change 73=11 → (70 : ZMod 73) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,9,19,12],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (71 : ZMod 73)
    change (71 : ZMod 73) ≠ 0 at hp
    change (71 : ZMod 73)-1 ≠ 0 at ha
    change (71 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((71 : ZMod 73)+1)) at hr
    change IsSquare (3-(71 : ZMod 73)) at hs
    change 73=7 → (71 : ZMod 73) ≠ 3 at h7
    change 73=11 → (71 : ZMod 73) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 73) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (72 : ZMod 73)
    change (72 : ZMod 73) ≠ 0 at hp
    change (72 : ZMod 73)-1 ≠ 0 at ha
    change (72 : ZMod 73)+1 ≠ 0 at hb
    change IsSquare (2*((72 : ZMod 73)+1)) at hr
    change IsSquare (3-(72 : ZMod 73)) at hs
    change 73=7 → (72 : ZMod 73) ≠ 3 at h7
    change 73=11 → (72 : ZMod 73) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts73

private instance prime79 : Fact (Nat.Prime 79) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts79 (p : ZMod 79) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 79=7 → p ≠ 3) (h11 : 79=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 79)
    change (0 : ZMod 79) ≠ 0 at hp
    change (0 : ZMod 79)-1 ≠ 0 at ha
    change (0 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 79)+1)) at hr
    change IsSquare (3-(0 : ZMod 79)) at hs
    change 79=7 → (0 : ZMod 79) ≠ 3 at h7
    change 79=11 → (0 : ZMod 79) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 79)
    change (1 : ZMod 79) ≠ 0 at hp
    change (1 : ZMod 79)-1 ≠ 0 at ha
    change (1 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 79)+1)) at hr
    change IsSquare (3-(1 : ZMod 79)) at hs
    change 79=7 → (1 : ZMod 79) ≠ 3 at h7
    change 79=11 → (1 : ZMod 79) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 79)
    change (2 : ZMod 79) ≠ 0 at hp
    change (2 : ZMod 79)-1 ≠ 0 at ha
    change (2 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 79)+1)) at hr
    change IsSquare (3-(2 : ZMod 79)) at hs
    change 79=7 → (2 : ZMod 79) ≠ 3 at h7
    change 79=11 → (2 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 79)
    change (3 : ZMod 79) ≠ 0 at hp
    change (3 : ZMod 79)-1 ≠ 0 at ha
    change (3 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 79)+1)) at hr
    change IsSquare (3-(3 : ZMod 79)) at hs
    change 79=7 → (3 : ZMod 79) ≠ 3 at h7
    change 79=11 → (3 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![3,18,36,22],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (4 : ZMod 79)
    change (4 : ZMod 79) ≠ 0 at hp
    change (4 : ZMod 79)-1 ≠ 0 at ha
    change (4 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 79)+1)) at hr
    change IsSquare (3-(4 : ZMod 79)) at hs
    change 79=7 → (4 : ZMod 79) ≠ 3 at h7
    change 79=11 → (4 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (78 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (5 : ZMod 79)
    change (5 : ZMod 79) ≠ 0 at hp
    change (5 : ZMod 79)-1 ≠ 0 at ha
    change (5 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 79)+1)) at hr
    change IsSquare (3-(5 : ZMod 79)) at hs
    change 79=7 → (5 : ZMod 79) ≠ 3 at h7
    change 79=11 → (5 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (6 : ZMod 79)
    change (6 : ZMod 79) ≠ 0 at hp
    change (6 : ZMod 79)-1 ≠ 0 at ha
    change (6 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 79)+1)) at hr
    change IsSquare (3-(6 : ZMod 79)) at hs
    change 79=7 → (6 : ZMod 79) ≠ 3 at h7
    change 79=11 → (6 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 79)
    change (7 : ZMod 79) ≠ 0 at hp
    change (7 : ZMod 79)-1 ≠ 0 at ha
    change (7 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 79)+1)) at hr
    change IsSquare (3-(7 : ZMod 79)) at hs
    change 79=7 → (7 : ZMod 79) ≠ 3 at h7
    change 79=11 → (7 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (75 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (8 : ZMod 79)
    change (8 : ZMod 79) ≠ 0 at hp
    change (8 : ZMod 79)-1 ≠ 0 at ha
    change (8 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 79)+1)) at hr
    change IsSquare (3-(8 : ZMod 79)) at hs
    change 79=7 → (8 : ZMod 79) ≠ 3 at h7
    change 79=11 → (8 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (74 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (9 : ZMod 79)
    change (9 : ZMod 79) ≠ 0 at hp
    change (9 : ZMod 79)-1 ≠ 0 at ha
    change (9 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 79)+1)) at hr
    change IsSquare (3-(9 : ZMod 79)) at hs
    change 79=7 → (9 : ZMod 79) ≠ 3 at h7
    change 79=11 → (9 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![3,0,35,27],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (10 : ZMod 79)
    change (10 : ZMod 79) ≠ 0 at hp
    change (10 : ZMod 79)-1 ≠ 0 at ha
    change (10 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 79)+1)) at hr
    change IsSquare (3-(10 : ZMod 79)) at hs
    change 79=7 → (10 : ZMod 79) ≠ 3 at h7
    change 79=11 → (10 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![22,0,26,39],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (11 : ZMod 79)
    change (11 : ZMod 79) ≠ 0 at hp
    change (11 : ZMod 79)-1 ≠ 0 at ha
    change (11 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 79)+1)) at hr
    change IsSquare (3-(11 : ZMod 79)) at hs
    change 79=7 → (11 : ZMod 79) ≠ 3 at h7
    change 79=11 → (11 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (12 : ZMod 79)
    change (12 : ZMod 79) ≠ 0 at hp
    change (12 : ZMod 79)-1 ≠ 0 at ha
    change (12 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 79)+1)) at hr
    change IsSquare (3-(12 : ZMod 79)) at hs
    change 79=7 → (12 : ZMod 79) ≠ 3 at h7
    change 79=11 → (12 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (70 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (13 : ZMod 79)
    change (13 : ZMod 79) ≠ 0 at hp
    change (13 : ZMod 79)-1 ≠ 0 at ha
    change (13 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 79)+1)) at hr
    change IsSquare (3-(13 : ZMod 79)) at hs
    change 79=7 → (13 : ZMod 79) ≠ 3 at h7
    change 79=11 → (13 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (14 : ZMod 79)
    change (14 : ZMod 79) ≠ 0 at hp
    change (14 : ZMod 79)-1 ≠ 0 at ha
    change (14 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 79)+1)) at hr
    change IsSquare (3-(14 : ZMod 79)) at hs
    change 79=7 → (14 : ZMod 79) ≠ 3 at h7
    change 79=11 → (14 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 79)
    change (15 : ZMod 79) ≠ 0 at hp
    change (15 : ZMod 79)-1 ≠ 0 at ha
    change (15 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 79)+1)) at hr
    change IsSquare (3-(15 : ZMod 79)) at hs
    change 79=7 → (15 : ZMod 79) ≠ 3 at h7
    change 79=11 → (15 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,29,36,4],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (16 : ZMod 79)
    change (16 : ZMod 79) ≠ 0 at hp
    change (16 : ZMod 79)-1 ≠ 0 at ha
    change (16 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 79)+1)) at hr
    change IsSquare (3-(16 : ZMod 79)) at hs
    change 79=7 → (16 : ZMod 79) ≠ 3 at h7
    change 79=11 → (16 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 79)
    change (17 : ZMod 79) ≠ 0 at hp
    change (17 : ZMod 79)-1 ≠ 0 at ha
    change (17 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 79)+1)) at hr
    change IsSquare (3-(17 : ZMod 79)) at hs
    change 79=7 → (17 : ZMod 79) ≠ 3 at h7
    change 79=11 → (17 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨12,![21,6,28,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (18 : ZMod 79)
    change (18 : ZMod 79) ≠ 0 at hp
    change (18 : ZMod 79)-1 ≠ 0 at ha
    change (18 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 79)+1)) at hr
    change IsSquare (3-(18 : ZMod 79)) at hs
    change 79=7 → (18 : ZMod 79) ≠ 3 at h7
    change 79=11 → (18 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,19,14,16],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (19 : ZMod 79)
    change (19 : ZMod 79) ≠ 0 at hp
    change (19 : ZMod 79)-1 ≠ 0 at ha
    change (19 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 79)+1)) at hr
    change IsSquare (3-(19 : ZMod 79)) at hs
    change 79=7 → (19 : ZMod 79) ≠ 3 at h7
    change 79=11 → (19 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (63 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (20 : ZMod 79)
    change (20 : ZMod 79) ≠ 0 at hp
    change (20 : ZMod 79)-1 ≠ 0 at ha
    change (20 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 79)+1)) at hr
    change IsSquare (3-(20 : ZMod 79)) at hs
    change 79=7 → (20 : ZMod 79) ≠ 3 at h7
    change 79=11 → (20 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![39,0,20,35],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (21 : ZMod 79)
    change (21 : ZMod 79) ≠ 0 at hp
    change (21 : ZMod 79)-1 ≠ 0 at ha
    change (21 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 79)+1)) at hr
    change IsSquare (3-(21 : ZMod 79)) at hs
    change 79=7 → (21 : ZMod 79) ≠ 3 at h7
    change 79=11 → (21 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (61 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (22 : ZMod 79)
    change (22 : ZMod 79) ≠ 0 at hp
    change (22 : ZMod 79)-1 ≠ 0 at ha
    change (22 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 79)+1)) at hr
    change IsSquare (3-(22 : ZMod 79)) at hs
    change 79=7 → (22 : ZMod 79) ≠ 3 at h7
    change 79=11 → (22 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (60 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (23 : ZMod 79)
    change (23 : ZMod 79) ≠ 0 at hp
    change (23 : ZMod 79)-1 ≠ 0 at ha
    change (23 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 79)+1)) at hr
    change IsSquare (3-(23 : ZMod 79)) at hs
    change 79=7 → (23 : ZMod 79) ≠ 3 at h7
    change 79=11 → (23 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (48 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (24 : ZMod 79)
    change (24 : ZMod 79) ≠ 0 at hp
    change (24 : ZMod 79)-1 ≠ 0 at ha
    change (24 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 79)+1)) at hr
    change IsSquare (3-(24 : ZMod 79)) at hs
    change 79=7 → (24 : ZMod 79) ≠ 3 at h7
    change 79=11 → (24 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (58 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (25 : ZMod 79)
    change (25 : ZMod 79) ≠ 0 at hp
    change (25 : ZMod 79)-1 ≠ 0 at ha
    change (25 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 79)+1)) at hr
    change IsSquare (3-(25 : ZMod 79)) at hs
    change 79=7 → (25 : ZMod 79) ≠ 3 at h7
    change 79=11 → (25 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (57 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (26 : ZMod 79)
    change (26 : ZMod 79) ≠ 0 at hp
    change (26 : ZMod 79)-1 ≠ 0 at ha
    change (26 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 79)+1)) at hr
    change IsSquare (3-(26 : ZMod 79)) at hs
    change 79=7 → (26 : ZMod 79) ≠ 3 at h7
    change 79=11 → (26 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (54 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (27 : ZMod 79)
    change (27 : ZMod 79) ≠ 0 at hp
    change (27 : ZMod 79)-1 ≠ 0 at ha
    change (27 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 79)+1)) at hr
    change IsSquare (3-(27 : ZMod 79)) at hs
    change 79=7 → (27 : ZMod 79) ≠ 3 at h7
    change 79=11 → (27 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (56 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (28 : ZMod 79)
    change (28 : ZMod 79) ≠ 0 at hp
    change (28 : ZMod 79)-1 ≠ 0 at ha
    change (28 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 79)+1)) at hr
    change IsSquare (3-(28 : ZMod 79)) at hs
    change 79=7 → (28 : ZMod 79) ≠ 3 at h7
    change 79=11 → (28 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (58 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (29 : ZMod 79)
    change (29 : ZMod 79) ≠ 0 at hp
    change (29 : ZMod 79)-1 ≠ 0 at ha
    change (29 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 79)+1)) at hr
    change IsSquare (3-(29 : ZMod 79)) at hs
    change 79=7 → (29 : ZMod 79) ≠ 3 at h7
    change 79=11 → (29 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (60 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (30 : ZMod 79)
    change (30 : ZMod 79) ≠ 0 at hp
    change (30 : ZMod 79)-1 ≠ 0 at ha
    change (30 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 79)+1)) at hr
    change IsSquare (3-(30 : ZMod 79)) at hs
    change 79=7 → (30 : ZMod 79) ≠ 3 at h7
    change 79=11 → (30 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,10,33,30],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (31 : ZMod 79)
    change (31 : ZMod 79) ≠ 0 at hp
    change (31 : ZMod 79)-1 ≠ 0 at ha
    change (31 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 79)+1)) at hr
    change IsSquare (3-(31 : ZMod 79)) at hs
    change 79=7 → (31 : ZMod 79) ≠ 3 at h7
    change 79=11 → (31 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,16,8,36],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (32 : ZMod 79)
    change (32 : ZMod 79) ≠ 0 at hp
    change (32 : ZMod 79)-1 ≠ 0 at ha
    change (32 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 79)+1)) at hr
    change IsSquare (3-(32 : ZMod 79)) at hs
    change 79=7 → (32 : ZMod 79) ≠ 3 at h7
    change 79=11 → (32 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (66 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (33 : ZMod 79)
    change (33 : ZMod 79) ≠ 0 at hp
    change (33 : ZMod 79)-1 ≠ 0 at ha
    change (33 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 79)+1)) at hr
    change IsSquare (3-(33 : ZMod 79)) at hs
    change 79=7 → (33 : ZMod 79) ≠ 3 at h7
    change 79=11 → (33 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (68 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (34 : ZMod 79)
    change (34 : ZMod 79) ≠ 0 at hp
    change (34 : ZMod 79)-1 ≠ 0 at ha
    change (34 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 79)+1)) at hr
    change IsSquare (3-(34 : ZMod 79)) at hs
    change 79=7 → (34 : ZMod 79) ≠ 3 at h7
    change 79=11 → (34 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (70 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (35 : ZMod 79)
    change (35 : ZMod 79) ≠ 0 at hp
    change (35 : ZMod 79)-1 ≠ 0 at ha
    change (35 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 79)+1)) at hr
    change IsSquare (3-(35 : ZMod 79)) at hs
    change 79=7 → (35 : ZMod 79) ≠ 3 at h7
    change 79=11 → (35 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (47 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (36 : ZMod 79)
    change (36 : ZMod 79) ≠ 0 at hp
    change (36 : ZMod 79)-1 ≠ 0 at ha
    change (36 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 79)+1)) at hr
    change IsSquare (3-(36 : ZMod 79)) at hs
    change 79=7 → (36 : ZMod 79) ≠ 3 at h7
    change 79=11 → (36 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (74 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (37 : ZMod 79)
    change (37 : ZMod 79) ≠ 0 at hp
    change (37 : ZMod 79)-1 ≠ 0 at ha
    change (37 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 79)+1)) at hr
    change IsSquare (3-(37 : ZMod 79)) at hs
    change 79=7 → (37 : ZMod 79) ≠ 3 at h7
    change 79=11 → (37 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![36,12,15,15],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (38 : ZMod 79)
    change (38 : ZMod 79) ≠ 0 at hp
    change (38 : ZMod 79)-1 ≠ 0 at ha
    change (38 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 79)+1)) at hr
    change IsSquare (3-(38 : ZMod 79)) at hs
    change 79=7 → (38 : ZMod 79) ≠ 3 at h7
    change 79=11 → (38 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (78 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (39 : ZMod 79)
    change (39 : ZMod 79) ≠ 0 at hp
    change (39 : ZMod 79)-1 ≠ 0 at ha
    change (39 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 79)+1)) at hr
    change IsSquare (3-(39 : ZMod 79)) at hs
    change 79=7 → (39 : ZMod 79) ≠ 3 at h7
    change 79=11 → (39 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (40 : ZMod 79)
    change (40 : ZMod 79) ≠ 0 at hp
    change (40 : ZMod 79)-1 ≠ 0 at ha
    change (40 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 79)+1)) at hr
    change IsSquare (3-(40 : ZMod 79)) at hs
    change 79=7 → (40 : ZMod 79) ≠ 3 at h7
    change 79=11 → (40 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (41 : ZMod 79)
    change (41 : ZMod 79) ≠ 0 at hp
    change (41 : ZMod 79)-1 ≠ 0 at ha
    change (41 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 79)+1)) at hr
    change IsSquare (3-(41 : ZMod 79)) at hs
    change 79=7 → (41 : ZMod 79) ≠ 3 at h7
    change 79=11 → (41 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (41 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (42 : ZMod 79)
    change (42 : ZMod 79) ≠ 0 at hp
    change (42 : ZMod 79)-1 ≠ 0 at ha
    change (42 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 79)+1)) at hr
    change IsSquare (3-(42 : ZMod 79)) at hs
    change 79=7 → (42 : ZMod 79) ≠ 3 at h7
    change 79=11 → (42 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (43 : ZMod 79)
    change (43 : ZMod 79) ≠ 0 at hp
    change (43 : ZMod 79)-1 ≠ 0 at ha
    change (43 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((43 : ZMod 79)+1)) at hr
    change IsSquare (3-(43 : ZMod 79)) at hs
    change 79=7 → (43 : ZMod 79) ≠ 3 at h7
    change 79=11 → (43 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (44 : ZMod 79)
    change (44 : ZMod 79) ≠ 0 at hp
    change (44 : ZMod 79)-1 ≠ 0 at ha
    change (44 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((44 : ZMod 79)+1)) at hr
    change IsSquare (3-(44 : ZMod 79)) at hs
    change 79=7 → (44 : ZMod 79) ≠ 3 at h7
    change 79=11 → (44 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,25,13,19],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (45 : ZMod 79)
    change (45 : ZMod 79) ≠ 0 at hp
    change (45 : ZMod 79)-1 ≠ 0 at ha
    change (45 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((45 : ZMod 79)+1)) at hr
    change IsSquare (3-(45 : ZMod 79)) at hs
    change 79=7 → (45 : ZMod 79) ≠ 3 at h7
    change 79=11 → (45 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (37 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (46 : ZMod 79)
    change (46 : ZMod 79) ≠ 0 at hp
    change (46 : ZMod 79)-1 ≠ 0 at ha
    change (46 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((46 : ZMod 79)+1)) at hr
    change IsSquare (3-(46 : ZMod 79)) at hs
    change 79=7 → (46 : ZMod 79) ≠ 3 at h7
    change 79=11 → (46 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (47 : ZMod 79)
    change (47 : ZMod 79) ≠ 0 at hp
    change (47 : ZMod 79)-1 ≠ 0 at ha
    change (47 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((47 : ZMod 79)+1)) at hr
    change IsSquare (3-(47 : ZMod 79)) at hs
    change 79=7 → (47 : ZMod 79) ≠ 3 at h7
    change 79=11 → (47 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (48 : ZMod 79)
    change (48 : ZMod 79) ≠ 0 at hp
    change (48 : ZMod 79)-1 ≠ 0 at ha
    change (48 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((48 : ZMod 79)+1)) at hr
    change IsSquare (3-(48 : ZMod 79)) at hs
    change 79=7 → (48 : ZMod 79) ≠ 3 at h7
    change 79=11 → (48 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (49 : ZMod 79)
    change (49 : ZMod 79) ≠ 0 at hp
    change (49 : ZMod 79)-1 ≠ 0 at ha
    change (49 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((49 : ZMod 79)+1)) at hr
    change IsSquare (3-(49 : ZMod 79)) at hs
    change 79=7 → (49 : ZMod 79) ≠ 3 at h7
    change 79=11 → (49 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (50 : ZMod 79)
    change (50 : ZMod 79) ≠ 0 at hp
    change (50 : ZMod 79)-1 ≠ 0 at ha
    change (50 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((50 : ZMod 79)+1)) at hr
    change IsSquare (3-(50 : ZMod 79)) at hs
    change 79=7 → (50 : ZMod 79) ≠ 3 at h7
    change 79=11 → (50 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![34,0,21,10],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (51 : ZMod 79)
    change (51 : ZMod 79) ≠ 0 at hp
    change (51 : ZMod 79)-1 ≠ 0 at ha
    change (51 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((51 : ZMod 79)+1)) at hr
    change IsSquare (3-(51 : ZMod 79)) at hs
    change 79=7 → (51 : ZMod 79) ≠ 3 at h7
    change 79=11 → (51 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![29,0,34,24],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (52 : ZMod 79)
    change (52 : ZMod 79) ≠ 0 at hp
    change (52 : ZMod 79)-1 ≠ 0 at ha
    change (52 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((52 : ZMod 79)+1)) at hr
    change IsSquare (3-(52 : ZMod 79)) at hs
    change 79=7 → (52 : ZMod 79) ≠ 3 at h7
    change 79=11 → (52 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (53 : ZMod 79)
    change (53 : ZMod 79) ≠ 0 at hp
    change (53 : ZMod 79)-1 ≠ 0 at ha
    change (53 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((53 : ZMod 79)+1)) at hr
    change IsSquare (3-(53 : ZMod 79)) at hs
    change 79=7 → (53 : ZMod 79) ≠ 3 at h7
    change 79=11 → (53 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (54 : ZMod 79)
    change (54 : ZMod 79) ≠ 0 at hp
    change (54 : ZMod 79)-1 ≠ 0 at ha
    change (54 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((54 : ZMod 79)+1)) at hr
    change IsSquare (3-(54 : ZMod 79)) at hs
    change 79=7 → (54 : ZMod 79) ≠ 3 at h7
    change 79=11 → (54 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (55 : ZMod 79)
    change (55 : ZMod 79) ≠ 0 at hp
    change (55 : ZMod 79)-1 ≠ 0 at ha
    change (55 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((55 : ZMod 79)+1)) at hr
    change IsSquare (3-(55 : ZMod 79)) at hs
    change 79=7 → (55 : ZMod 79) ≠ 3 at h7
    change 79=11 → (55 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (56 : ZMod 79)
    change (56 : ZMod 79) ≠ 0 at hp
    change (56 : ZMod 79)-1 ≠ 0 at ha
    change (56 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((56 : ZMod 79)+1)) at hr
    change IsSquare (3-(56 : ZMod 79)) at hs
    change 79=7 → (56 : ZMod 79) ≠ 3 at h7
    change 79=11 → (56 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (57 : ZMod 79)
    change (57 : ZMod 79) ≠ 0 at hp
    change (57 : ZMod 79)-1 ≠ 0 at ha
    change (57 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((57 : ZMod 79)+1)) at hr
    change IsSquare (3-(57 : ZMod 79)) at hs
    change 79=7 → (57 : ZMod 79) ≠ 3 at h7
    change 79=11 → (57 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (37 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (58 : ZMod 79)
    change (58 : ZMod 79) ≠ 0 at hp
    change (58 : ZMod 79)-1 ≠ 0 at ha
    change (58 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((58 : ZMod 79)+1)) at hr
    change IsSquare (3-(58 : ZMod 79)) at hs
    change 79=7 → (58 : ZMod 79) ≠ 3 at h7
    change 79=11 → (58 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (59 : ZMod 79)
    change (59 : ZMod 79) ≠ 0 at hp
    change (59 : ZMod 79)-1 ≠ 0 at ha
    change (59 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((59 : ZMod 79)+1)) at hr
    change IsSquare (3-(59 : ZMod 79)) at hs
    change 79=7 → (59 : ZMod 79) ≠ 3 at h7
    change 79=11 → (59 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (41 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (60 : ZMod 79)
    change (60 : ZMod 79) ≠ 0 at hp
    change (60 : ZMod 79)-1 ≠ 0 at ha
    change (60 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((60 : ZMod 79)+1)) at hr
    change IsSquare (3-(60 : ZMod 79)) at hs
    change 79=7 → (60 : ZMod 79) ≠ 3 at h7
    change 79=11 → (60 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (61 : ZMod 79)
    change (61 : ZMod 79) ≠ 0 at hp
    change (61 : ZMod 79)-1 ≠ 0 at ha
    change (61 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((61 : ZMod 79)+1)) at hr
    change IsSquare (3-(61 : ZMod 79)) at hs
    change 79=7 → (61 : ZMod 79) ≠ 3 at h7
    change 79=11 → (61 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,14,19,33],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (62 : ZMod 79)
    change (62 : ZMod 79) ≠ 0 at hp
    change (62 : ZMod 79)-1 ≠ 0 at ha
    change (62 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((62 : ZMod 79)+1)) at hr
    change IsSquare (3-(62 : ZMod 79)) at hs
    change 79=7 → (62 : ZMod 79) ≠ 3 at h7
    change 79=11 → (62 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (47 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (63 : ZMod 79)
    change (63 : ZMod 79) ≠ 0 at hp
    change (63 : ZMod 79)-1 ≠ 0 at ha
    change (63 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((63 : ZMod 79)+1)) at hr
    change IsSquare (3-(63 : ZMod 79)) at hs
    change 79=7 → (63 : ZMod 79) ≠ 3 at h7
    change 79=11 → (63 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![30,13,14,31],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (64 : ZMod 79)
    change (64 : ZMod 79) ≠ 0 at hp
    change (64 : ZMod 79)-1 ≠ 0 at ha
    change (64 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((64 : ZMod 79)+1)) at hr
    change IsSquare (3-(64 : ZMod 79)) at hs
    change 79=7 → (64 : ZMod 79) ≠ 3 at h7
    change 79=11 → (64 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,36,29,12],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (65 : ZMod 79)
    change (65 : ZMod 79) ≠ 0 at hp
    change (65 : ZMod 79)-1 ≠ 0 at ha
    change (65 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((65 : ZMod 79)+1)) at hr
    change IsSquare (3-(65 : ZMod 79)) at hs
    change 79=7 → (65 : ZMod 79) ≠ 3 at h7
    change 79=11 → (65 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (53 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (66 : ZMod 79)
    change (66 : ZMod 79) ≠ 0 at hp
    change (66 : ZMod 79)-1 ≠ 0 at ha
    change (66 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((66 : ZMod 79)+1)) at hr
    change IsSquare (3-(66 : ZMod 79)) at hs
    change 79=7 → (66 : ZMod 79) ≠ 3 at h7
    change 79=11 → (66 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![35,24,33,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (67 : ZMod 79)
    change (67 : ZMod 79) ≠ 0 at hp
    change (67 : ZMod 79)-1 ≠ 0 at ha
    change (67 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((67 : ZMod 79)+1)) at hr
    change IsSquare (3-(67 : ZMod 79)) at hs
    change 79=7 → (67 : ZMod 79) ≠ 3 at h7
    change 79=11 → (67 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (57 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (68 : ZMod 79)
    change (68 : ZMod 79) ≠ 0 at hp
    change (68 : ZMod 79)-1 ≠ 0 at ha
    change (68 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((68 : ZMod 79)+1)) at hr
    change IsSquare (3-(68 : ZMod 79)) at hs
    change 79=7 → (68 : ZMod 79) ≠ 3 at h7
    change 79=11 → (68 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (59 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (69 : ZMod 79)
    change (69 : ZMod 79) ≠ 0 at hp
    change (69 : ZMod 79)-1 ≠ 0 at ha
    change (69 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((69 : ZMod 79)+1)) at hr
    change IsSquare (3-(69 : ZMod 79)) at hs
    change 79=7 → (69 : ZMod 79) ≠ 3 at h7
    change 79=11 → (69 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (61 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (70 : ZMod 79)
    change (70 : ZMod 79) ≠ 0 at hp
    change (70 : ZMod 79)-1 ≠ 0 at ha
    change (70 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((70 : ZMod 79)+1)) at hr
    change IsSquare (3-(70 : ZMod 79)) at hs
    change 79=7 → (70 : ZMod 79) ≠ 3 at h7
    change 79=11 → (70 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (63 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (71 : ZMod 79)
    change (71 : ZMod 79) ≠ 0 at hp
    change (71 : ZMod 79)-1 ≠ 0 at ha
    change (71 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((71 : ZMod 79)+1)) at hr
    change IsSquare (3-(71 : ZMod 79)) at hs
    change 79=7 → (71 : ZMod 79) ≠ 3 at h7
    change 79=11 → (71 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,27,12,25],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (72 : ZMod 79)
    change (72 : ZMod 79) ≠ 0 at hp
    change (72 : ZMod 79)-1 ≠ 0 at ha
    change (72 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((72 : ZMod 79)+1)) at hr
    change IsSquare (3-(72 : ZMod 79)) at hs
    change 79=7 → (72 : ZMod 79) ≠ 3 at h7
    change 79=11 → (72 : ZMod 79) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,4,15,28],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (73 : ZMod 79)
    change (73 : ZMod 79) ≠ 0 at hp
    change (73 : ZMod 79)-1 ≠ 0 at ha
    change (73 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((73 : ZMod 79)+1)) at hr
    change IsSquare (3-(73 : ZMod 79)) at hs
    change 79=7 → (73 : ZMod 79) ≠ 3 at h7
    change 79=11 → (73 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (69 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (74 : ZMod 79)
    change (74 : ZMod 79) ≠ 0 at hp
    change (74 : ZMod 79)-1 ≠ 0 at ha
    change (74 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((74 : ZMod 79)+1)) at hr
    change IsSquare (3-(74 : ZMod 79)) at hs
    change 79=7 → (74 : ZMod 79) ≠ 3 at h7
    change 79=11 → (74 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (71 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (75 : ZMod 79)
    change (75 : ZMod 79) ≠ 0 at hp
    change (75 : ZMod 79)-1 ≠ 0 at ha
    change (75 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((75 : ZMod 79)+1)) at hr
    change IsSquare (3-(75 : ZMod 79)) at hs
    change 79=7 → (75 : ZMod 79) ≠ 3 at h7
    change 79=11 → (75 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (76 : ZMod 79)
    change (76 : ZMod 79) ≠ 0 at hp
    change (76 : ZMod 79)-1 ≠ 0 at ha
    change (76 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((76 : ZMod 79)+1)) at hr
    change IsSquare (3-(76 : ZMod 79)) at hs
    change 79=7 → (76 : ZMod 79) ≠ 3 at h7
    change 79=11 → (76 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (75 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (77 : ZMod 79)
    change (77 : ZMod 79) ≠ 0 at hp
    change (77 : ZMod 79)-1 ≠ 0 at ha
    change (77 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((77 : ZMod 79)+1)) at hr
    change IsSquare (3-(77 : ZMod 79)) at hs
    change 79=7 → (77 : ZMod 79) ≠ 3 at h7
    change 79=11 → (77 : ZMod 79) ≠ 5 at h11
    have hn : ¬IsSquare (77 : ZMod 79) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (78 : ZMod 79)
    change (78 : ZMod 79) ≠ 0 at hp
    change (78 : ZMod 79)-1 ≠ 0 at ha
    change (78 : ZMod 79)+1 ≠ 0 at hb
    change IsSquare (2*((78 : ZMod 79)+1)) at hr
    change IsSquare (3-(78 : ZMod 79)) at hs
    change 79=7 → (78 : ZMod 79) ≠ 3 at h7
    change 79=11 → (78 : ZMod 79) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts79

private instance prime83 : Fact (Nat.Prime 83) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts83 (p : ZMod 83) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 83=7 → p ≠ 3) (h11 : 83=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 83)
    change (0 : ZMod 83) ≠ 0 at hp
    change (0 : ZMod 83)-1 ≠ 0 at ha
    change (0 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 83)+1)) at hr
    change IsSquare (3-(0 : ZMod 83)) at hs
    change 83=7 → (0 : ZMod 83) ≠ 3 at h7
    change 83=11 → (0 : ZMod 83) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 83)
    change (1 : ZMod 83) ≠ 0 at hp
    change (1 : ZMod 83)-1 ≠ 0 at ha
    change (1 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 83)+1)) at hr
    change IsSquare (3-(1 : ZMod 83)) at hs
    change 83=7 → (1 : ZMod 83) ≠ 3 at h7
    change 83=11 → (1 : ZMod 83) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 83)
    change (2 : ZMod 83) ≠ 0 at hp
    change (2 : ZMod 83)-1 ≠ 0 at ha
    change (2 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 83)+1)) at hr
    change IsSquare (3-(2 : ZMod 83)) at hs
    change 83=7 → (2 : ZMod 83) ≠ 3 at h7
    change 83=11 → (2 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 83)
    change (3 : ZMod 83) ≠ 0 at hp
    change (3 : ZMod 83)-1 ≠ 0 at ha
    change (3 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 83)+1)) at hr
    change IsSquare (3-(3 : ZMod 83)) at hs
    change 83=7 → (3 : ZMod 83) ≠ 3 at h7
    change 83=11 → (3 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (4 : ZMod 83)
    change (4 : ZMod 83) ≠ 0 at hp
    change (4 : ZMod 83)-1 ≠ 0 at ha
    change (4 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 83)+1)) at hr
    change IsSquare (3-(4 : ZMod 83)) at hs
    change 83=7 → (4 : ZMod 83) ≠ 3 at h7
    change 83=11 → (4 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (82 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (5 : ZMod 83)
    change (5 : ZMod 83) ≠ 0 at hp
    change (5 : ZMod 83)-1 ≠ 0 at ha
    change (5 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 83)+1)) at hr
    change IsSquare (3-(5 : ZMod 83)) at hs
    change 83=7 → (5 : ZMod 83) ≠ 3 at h7
    change 83=11 → (5 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![14,17,1,14],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (6 : ZMod 83)
    change (6 : ZMod 83) ≠ 0 at hp
    change (6 : ZMod 83)-1 ≠ 0 at ha
    change (6 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 83)+1)) at hr
    change IsSquare (3-(6 : ZMod 83)) at hs
    change 83=7 → (6 : ZMod 83) ≠ 3 at h7
    change 83=11 → (6 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 83)
    change (7 : ZMod 83) ≠ 0 at hp
    change (7 : ZMod 83)-1 ≠ 0 at ha
    change (7 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 83)+1)) at hr
    change IsSquare (3-(7 : ZMod 83)) at hs
    change 83=7 → (7 : ZMod 83) ≠ 3 at h7
    change 83=11 → (7 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (79 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (8 : ZMod 83)
    change (8 : ZMod 83) ≠ 0 at hp
    change (8 : ZMod 83)-1 ≠ 0 at ha
    change (8 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 83)+1)) at hr
    change IsSquare (3-(8 : ZMod 83)) at hs
    change 83=7 → (8 : ZMod 83) ≠ 3 at h7
    change 83=11 → (8 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (18 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (9 : ZMod 83)
    change (9 : ZMod 83) ≠ 0 at hp
    change (9 : ZMod 83)-1 ≠ 0 at ha
    change (9 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 83)+1)) at hr
    change IsSquare (3-(9 : ZMod 83)) at hs
    change 83=7 → (9 : ZMod 83) ≠ 3 at h7
    change 83=11 → (9 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (10 : ZMod 83)
    change (10 : ZMod 83) ≠ 0 at hp
    change (10 : ZMod 83)-1 ≠ 0 at ha
    change (10 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 83)+1)) at hr
    change IsSquare (3-(10 : ZMod 83)) at hs
    change 83=7 → (10 : ZMod 83) ≠ 3 at h7
    change 83=11 → (10 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (22 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (11 : ZMod 83)
    change (11 : ZMod 83) ≠ 0 at hp
    change (11 : ZMod 83)-1 ≠ 0 at ha
    change (11 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 83)+1)) at hr
    change IsSquare (3-(11 : ZMod 83)) at hs
    change 83=7 → (11 : ZMod 83) ≠ 3 at h7
    change 83=11 → (11 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (12 : ZMod 83)
    change (12 : ZMod 83) ≠ 0 at hp
    change (12 : ZMod 83)-1 ≠ 0 at ha
    change (12 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 83)+1)) at hr
    change IsSquare (3-(12 : ZMod 83)) at hs
    change 83=7 → (12 : ZMod 83) ≠ 3 at h7
    change 83=11 → (12 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (74 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (13 : ZMod 83)
    change (13 : ZMod 83) ≠ 0 at hp
    change (13 : ZMod 83)-1 ≠ 0 at ha
    change (13 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 83)+1)) at hr
    change IsSquare (3-(13 : ZMod 83)) at hs
    change 83=7 → (13 : ZMod 83) ≠ 3 at h7
    change 83=11 → (13 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (73 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (14 : ZMod 83)
    change (14 : ZMod 83) ≠ 0 at hp
    change (14 : ZMod 83)-1 ≠ 0 at ha
    change (14 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 83)+1)) at hr
    change IsSquare (3-(14 : ZMod 83)) at hs
    change 83=7 → (14 : ZMod 83) ≠ 3 at h7
    change 83=11 → (14 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (72 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (15 : ZMod 83)
    change (15 : ZMod 83) ≠ 0 at hp
    change (15 : ZMod 83)-1 ≠ 0 at ha
    change (15 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 83)+1)) at hr
    change IsSquare (3-(15 : ZMod 83)) at hs
    change 83=7 → (15 : ZMod 83) ≠ 3 at h7
    change 83=11 → (15 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (32 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (16 : ZMod 83)
    change (16 : ZMod 83) ≠ 0 at hp
    change (16 : ZMod 83)-1 ≠ 0 at ha
    change (16 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 83)+1)) at hr
    change IsSquare (3-(16 : ZMod 83)) at hs
    change 83=7 → (16 : ZMod 83) ≠ 3 at h7
    change 83=11 → (16 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 83)
    change (17 : ZMod 83) ≠ 0 at hp
    change (17 : ZMod 83)-1 ≠ 0 at ha
    change (17 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 83)+1)) at hr
    change IsSquare (3-(17 : ZMod 83)) at hs
    change 83=7 → (17 : ZMod 83) ≠ 3 at h7
    change 83=11 → (17 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨16,![40,27,23,5],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (18 : ZMod 83)
    change (18 : ZMod 83) ≠ 0 at hp
    change (18 : ZMod 83)-1 ≠ 0 at ha
    change (18 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 83)+1)) at hr
    change IsSquare (3-(18 : ZMod 83)) at hs
    change 83=7 → (18 : ZMod 83) ≠ 3 at h7
    change 83=11 → (18 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![5,2,10,11],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (19 : ZMod 83)
    change (19 : ZMod 83) ≠ 0 at hp
    change (19 : ZMod 83)-1 ≠ 0 at ha
    change (19 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 83)+1)) at hr
    change IsSquare (3-(19 : ZMod 83)) at hs
    change 83=7 → (19 : ZMod 83) ≠ 3 at h7
    change 83=11 → (19 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (67 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (20 : ZMod 83)
    change (20 : ZMod 83) ≠ 0 at hp
    change (20 : ZMod 83)-1 ≠ 0 at ha
    change (20 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 83)+1)) at hr
    change IsSquare (3-(20 : ZMod 83)) at hs
    change 83=7 → (20 : ZMod 83) ≠ 3 at h7
    change 83=11 → (20 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (42 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (21 : ZMod 83)
    change (21 : ZMod 83) ≠ 0 at hp
    change (21 : ZMod 83)-1 ≠ 0 at ha
    change (21 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 83)+1)) at hr
    change IsSquare (3-(21 : ZMod 83)) at hs
    change 83=7 → (21 : ZMod 83) ≠ 3 at h7
    change 83=11 → (21 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨26,![31,2,21,25],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (22 : ZMod 83)
    change (22 : ZMod 83) ≠ 0 at hp
    change (22 : ZMod 83)-1 ≠ 0 at ha
    change (22 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 83)+1)) at hr
    change IsSquare (3-(22 : ZMod 83)) at hs
    change 83=7 → (22 : ZMod 83) ≠ 3 at h7
    change 83=11 → (22 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (46 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (23 : ZMod 83)
    change (23 : ZMod 83) ≠ 0 at hp
    change (23 : ZMod 83)-1 ≠ 0 at ha
    change (23 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 83)+1)) at hr
    change IsSquare (3-(23 : ZMod 83)) at hs
    change 83=7 → (23 : ZMod 83) ≠ 3 at h7
    change 83=11 → (23 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨10,![8,8,14,24],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (24 : ZMod 83)
    change (24 : ZMod 83) ≠ 0 at hp
    change (24 : ZMod 83)-1 ≠ 0 at ha
    change (24 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 83)+1)) at hr
    change IsSquare (3-(24 : ZMod 83)) at hs
    change 83=7 → (24 : ZMod 83) ≠ 3 at h7
    change 83=11 → (24 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (50 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (25 : ZMod 83)
    change (25 : ZMod 83) ≠ 0 at hp
    change (25 : ZMod 83)-1 ≠ 0 at ha
    change (25 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 83)+1)) at hr
    change IsSquare (3-(25 : ZMod 83)) at hs
    change 83=7 → (25 : ZMod 83) ≠ 3 at h7
    change 83=11 → (25 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (52 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (26 : ZMod 83)
    change (26 : ZMod 83) ≠ 0 at hp
    change (26 : ZMod 83)-1 ≠ 0 at ha
    change (26 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 83)+1)) at hr
    change IsSquare (3-(26 : ZMod 83)) at hs
    change 83=7 → (26 : ZMod 83) ≠ 3 at h7
    change 83=11 → (26 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (54 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (27 : ZMod 83)
    change (27 : ZMod 83) ≠ 0 at hp
    change (27 : ZMod 83)-1 ≠ 0 at ha
    change (27 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 83)+1)) at hr
    change IsSquare (3-(27 : ZMod 83)) at hs
    change 83=7 → (27 : ZMod 83) ≠ 3 at h7
    change 83=11 → (27 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (56 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (28 : ZMod 83)
    change (28 : ZMod 83) ≠ 0 at hp
    change (28 : ZMod 83)-1 ≠ 0 at ha
    change (28 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 83)+1)) at hr
    change IsSquare (3-(28 : ZMod 83)) at hs
    change 83=7 → (28 : ZMod 83) ≠ 3 at h7
    change 83=11 → (28 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (58 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (29 : ZMod 83)
    change (29 : ZMod 83) ≠ 0 at hp
    change (29 : ZMod 83)-1 ≠ 0 at ha
    change (29 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 83)+1)) at hr
    change IsSquare (3-(29 : ZMod 83)) at hs
    change 83=7 → (29 : ZMod 83) ≠ 3 at h7
    change 83=11 → (29 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (60 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (30 : ZMod 83)
    change (30 : ZMod 83) ≠ 0 at hp
    change (30 : ZMod 83)-1 ≠ 0 at ha
    change (30 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 83)+1)) at hr
    change IsSquare (3-(30 : ZMod 83)) at hs
    change 83=7 → (30 : ZMod 83) ≠ 3 at h7
    change 83=11 → (30 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (62 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (31 : ZMod 83)
    change (31 : ZMod 83) ≠ 0 at hp
    change (31 : ZMod 83)-1 ≠ 0 at ha
    change (31 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 83)+1)) at hr
    change IsSquare (3-(31 : ZMod 83)) at hs
    change 83=7 → (31 : ZMod 83) ≠ 3 at h7
    change 83=11 → (31 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (55 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (32 : ZMod 83)
    change (32 : ZMod 83) ≠ 0 at hp
    change (32 : ZMod 83)-1 ≠ 0 at ha
    change (32 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 83)+1)) at hr
    change IsSquare (3-(32 : ZMod 83)) at hs
    change 83=7 → (32 : ZMod 83) ≠ 3 at h7
    change 83=11 → (32 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (66 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (33 : ZMod 83)
    change (33 : ZMod 83) ≠ 0 at hp
    change (33 : ZMod 83)-1 ≠ 0 at ha
    change (33 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 83)+1)) at hr
    change IsSquare (3-(33 : ZMod 83)) at hs
    change 83=7 → (33 : ZMod 83) ≠ 3 at h7
    change 83=11 → (33 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (53 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (34 : ZMod 83)
    change (34 : ZMod 83) ≠ 0 at hp
    change (34 : ZMod 83)-1 ≠ 0 at ha
    change (34 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 83)+1)) at hr
    change IsSquare (3-(34 : ZMod 83)) at hs
    change 83=7 → (34 : ZMod 83) ≠ 3 at h7
    change 83=11 → (34 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (52 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (35 : ZMod 83)
    change (35 : ZMod 83) ≠ 0 at hp
    change (35 : ZMod 83)-1 ≠ 0 at ha
    change (35 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 83)+1)) at hr
    change IsSquare (3-(35 : ZMod 83)) at hs
    change 83=7 → (35 : ZMod 83) ≠ 3 at h7
    change 83=11 → (35 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (72 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (36 : ZMod 83)
    change (36 : ZMod 83) ≠ 0 at hp
    change (36 : ZMod 83)-1 ≠ 0 at ha
    change (36 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 83)+1)) at hr
    change IsSquare (3-(36 : ZMod 83)) at hs
    change 83=7 → (36 : ZMod 83) ≠ 3 at h7
    change 83=11 → (36 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (74 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (37 : ZMod 83)
    change (37 : ZMod 83) ≠ 0 at hp
    change (37 : ZMod 83)-1 ≠ 0 at ha
    change (37 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 83)+1)) at hr
    change IsSquare (3-(37 : ZMod 83)) at hs
    change 83=7 → (37 : ZMod 83) ≠ 3 at h7
    change 83=11 → (37 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (76 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (38 : ZMod 83)
    change (38 : ZMod 83) ≠ 0 at hp
    change (38 : ZMod 83)-1 ≠ 0 at ha
    change (38 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 83)+1)) at hr
    change IsSquare (3-(38 : ZMod 83)) at hs
    change 83=7 → (38 : ZMod 83) ≠ 3 at h7
    change 83=11 → (38 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨9,![33,29,38,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (39 : ZMod 83)
    change (39 : ZMod 83) ≠ 0 at hp
    change (39 : ZMod 83)-1 ≠ 0 at ha
    change (39 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 83)+1)) at hr
    change IsSquare (3-(39 : ZMod 83)) at hs
    change 83=7 → (39 : ZMod 83) ≠ 3 at h7
    change 83=11 → (39 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (80 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (40 : ZMod 83)
    change (40 : ZMod 83) ≠ 0 at hp
    change (40 : ZMod 83)-1 ≠ 0 at ha
    change (40 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 83)+1)) at hr
    change IsSquare (3-(40 : ZMod 83)) at hs
    change 83=7 → (40 : ZMod 83) ≠ 3 at h7
    change 83=11 → (40 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (82 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (41 : ZMod 83)
    change (41 : ZMod 83) ≠ 0 at hp
    change (41 : ZMod 83)-1 ≠ 0 at ha
    change (41 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 83)+1)) at hr
    change IsSquare (3-(41 : ZMod 83)) at hs
    change 83=7 → (41 : ZMod 83) ≠ 3 at h7
    change 83=11 → (41 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (45 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (42 : ZMod 83)
    change (42 : ZMod 83) ≠ 0 at hp
    change (42 : ZMod 83)-1 ≠ 0 at ha
    change (42 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 83)+1)) at hr
    change IsSquare (3-(42 : ZMod 83)) at hs
    change 83=7 → (42 : ZMod 83) ≠ 3 at h7
    change 83=11 → (42 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![13,24,41,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (43 : ZMod 83)
    change (43 : ZMod 83) ≠ 0 at hp
    change (43 : ZMod 83)-1 ≠ 0 at ha
    change (43 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((43 : ZMod 83)+1)) at hr
    change IsSquare (3-(43 : ZMod 83)) at hs
    change 83=7 → (43 : ZMod 83) ≠ 3 at h7
    change 83=11 → (43 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (44 : ZMod 83)
    change (44 : ZMod 83) ≠ 0 at hp
    change (44 : ZMod 83)-1 ≠ 0 at ha
    change (44 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((44 : ZMod 83)+1)) at hr
    change IsSquare (3-(44 : ZMod 83)) at hs
    change 83=7 → (44 : ZMod 83) ≠ 3 at h7
    change 83=11 → (44 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (42 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (45 : ZMod 83)
    change (45 : ZMod 83) ≠ 0 at hp
    change (45 : ZMod 83)-1 ≠ 0 at ha
    change (45 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((45 : ZMod 83)+1)) at hr
    change IsSquare (3-(45 : ZMod 83)) at hs
    change 83=7 → (45 : ZMod 83) ≠ 3 at h7
    change 83=11 → (45 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨6,![41,5,35,12],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (46 : ZMod 83)
    change (46 : ZMod 83) ≠ 0 at hp
    change (46 : ZMod 83)-1 ≠ 0 at ha
    change (46 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((46 : ZMod 83)+1)) at hr
    change IsSquare (3-(46 : ZMod 83)) at hs
    change 83=7 → (46 : ZMod 83) ≠ 3 at h7
    change 83=11 → (46 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨8,![6,7,4,18],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (47 : ZMod 83)
    change (47 : ZMod 83) ≠ 0 at hp
    change (47 : ZMod 83)-1 ≠ 0 at ha
    change (47 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((47 : ZMod 83)+1)) at hr
    change IsSquare (3-(47 : ZMod 83)) at hs
    change 83=7 → (47 : ZMod 83) ≠ 3 at h7
    change 83=11 → (47 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (48 : ZMod 83)
    change (48 : ZMod 83) ≠ 0 at hp
    change (48 : ZMod 83)-1 ≠ 0 at ha
    change (48 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((48 : ZMod 83)+1)) at hr
    change IsSquare (3-(48 : ZMod 83)) at hs
    change 83=7 → (48 : ZMod 83) ≠ 3 at h7
    change 83=11 → (48 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (49 : ZMod 83)
    change (49 : ZMod 83) ≠ 0 at hp
    change (49 : ZMod 83)-1 ≠ 0 at ha
    change (49 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((49 : ZMod 83)+1)) at hr
    change IsSquare (3-(49 : ZMod 83)) at hs
    change 83=7 → (49 : ZMod 83) ≠ 3 at h7
    change 83=11 → (49 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![8,21,20,32],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (50 : ZMod 83)
    change (50 : ZMod 83) ≠ 0 at hp
    change (50 : ZMod 83)-1 ≠ 0 at ha
    change (50 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((50 : ZMod 83)+1)) at hr
    change IsSquare (3-(50 : ZMod 83)) at hs
    change 83=7 → (50 : ZMod 83) ≠ 3 at h7
    change 83=11 → (50 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (51 : ZMod 83)
    change (51 : ZMod 83) ≠ 0 at hp
    change (51 : ZMod 83)-1 ≠ 0 at ha
    change (51 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((51 : ZMod 83)+1)) at hr
    change IsSquare (3-(51 : ZMod 83)) at hs
    change 83=7 → (51 : ZMod 83) ≠ 3 at h7
    change 83=11 → (51 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (52 : ZMod 83)
    change (52 : ZMod 83) ≠ 0 at hp
    change (52 : ZMod 83)-1 ≠ 0 at ha
    change (52 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((52 : ZMod 83)+1)) at hr
    change IsSquare (3-(52 : ZMod 83)) at hs
    change 83=7 → (52 : ZMod 83) ≠ 3 at h7
    change 83=11 → (52 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (53 : ZMod 83)
    change (53 : ZMod 83) ≠ 0 at hp
    change (53 : ZMod 83)-1 ≠ 0 at ha
    change (53 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((53 : ZMod 83)+1)) at hr
    change IsSquare (3-(53 : ZMod 83)) at hs
    change 83=7 → (53 : ZMod 83) ≠ 3 at h7
    change 83=11 → (53 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨2,![40,41,18,18],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (54 : ZMod 83)
    change (54 : ZMod 83) ≠ 0 at hp
    change (54 : ZMod 83)-1 ≠ 0 at ha
    change (54 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((54 : ZMod 83)+1)) at hr
    change IsSquare (3-(54 : ZMod 83)) at hs
    change 83=7 → (54 : ZMod 83) ≠ 3 at h7
    change 83=11 → (54 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (32 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (55 : ZMod 83)
    change (55 : ZMod 83) ≠ 0 at hp
    change (55 : ZMod 83)-1 ≠ 0 at ha
    change (55 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((55 : ZMod 83)+1)) at hr
    change IsSquare (3-(55 : ZMod 83)) at hs
    change 83=7 → (55 : ZMod 83) ≠ 3 at h7
    change 83=11 → (55 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨2,![39,5,2,9],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (56 : ZMod 83)
    change (56 : ZMod 83) ≠ 0 at hp
    change (56 : ZMod 83)-1 ≠ 0 at ha
    change (56 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((56 : ZMod 83)+1)) at hr
    change IsSquare (3-(56 : ZMod 83)) at hs
    change 83=7 → (56 : ZMod 83) ≠ 3 at h7
    change 83=11 → (56 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨2,![19,39,33,1],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (57 : ZMod 83)
    change (57 : ZMod 83) ≠ 0 at hp
    change (57 : ZMod 83)-1 ≠ 0 at ha
    change (57 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((57 : ZMod 83)+1)) at hr
    change IsSquare (3-(57 : ZMod 83)) at hs
    change 83=7 → (57 : ZMod 83) ≠ 3 at h7
    change 83=11 → (57 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨2,![23,19,4,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (58 : ZMod 83)
    change (58 : ZMod 83) ≠ 0 at hp
    change (58 : ZMod 83)-1 ≠ 0 at ha
    change (58 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((58 : ZMod 83)+1)) at hr
    change IsSquare (3-(58 : ZMod 83)) at hs
    change 83=7 → (58 : ZMod 83) ≠ 3 at h7
    change 83=11 → (58 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (59 : ZMod 83)
    change (59 : ZMod 83) ≠ 0 at hp
    change (59 : ZMod 83)-1 ≠ 0 at ha
    change (59 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((59 : ZMod 83)+1)) at hr
    change IsSquare (3-(59 : ZMod 83)) at hs
    change 83=7 → (59 : ZMod 83) ≠ 3 at h7
    change 83=11 → (59 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨10,![3,31,18,15],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (60 : ZMod 83)
    change (60 : ZMod 83) ≠ 0 at hp
    change (60 : ZMod 83)-1 ≠ 0 at ha
    change (60 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((60 : ZMod 83)+1)) at hr
    change IsSquare (3-(60 : ZMod 83)) at hs
    change 83=7 → (60 : ZMod 83) ≠ 3 at h7
    change 83=11 → (60 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (61 : ZMod 83)
    change (61 : ZMod 83) ≠ 0 at hp
    change (61 : ZMod 83)-1 ≠ 0 at ha
    change (61 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((61 : ZMod 83)+1)) at hr
    change IsSquare (3-(61 : ZMod 83)) at hs
    change 83=7 → (61 : ZMod 83) ≠ 3 at h7
    change 83=11 → (61 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨10,![19,1,6,9],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (62 : ZMod 83)
    change (62 : ZMod 83) ≠ 0 at hp
    change (62 : ZMod 83)-1 ≠ 0 at ha
    change (62 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((62 : ZMod 83)+1)) at hr
    change IsSquare (3-(62 : ZMod 83)) at hs
    change 83=7 → (62 : ZMod 83) ≠ 3 at h7
    change 83=11 → (62 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (63 : ZMod 83)
    change (63 : ZMod 83) ≠ 0 at hp
    change (63 : ZMod 83)-1 ≠ 0 at ha
    change (63 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((63 : ZMod 83)+1)) at hr
    change IsSquare (3-(63 : ZMod 83)) at hs
    change 83=7 → (63 : ZMod 83) ≠ 3 at h7
    change 83=11 → (63 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (45 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (64 : ZMod 83)
    change (64 : ZMod 83) ≠ 0 at hp
    change (64 : ZMod 83)-1 ≠ 0 at ha
    change (64 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((64 : ZMod 83)+1)) at hr
    change IsSquare (3-(64 : ZMod 83)) at hs
    change 83=7 → (64 : ZMod 83) ≠ 3 at h7
    change 83=11 → (64 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (47 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (65 : ZMod 83)
    change (65 : ZMod 83) ≠ 0 at hp
    change (65 : ZMod 83)-1 ≠ 0 at ha
    change (65 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((65 : ZMod 83)+1)) at hr
    change IsSquare (3-(65 : ZMod 83)) at hs
    change 83=7 → (65 : ZMod 83) ≠ 3 at h7
    change 83=11 → (65 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![19,16,14,3],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (66 : ZMod 83)
    change (66 : ZMod 83) ≠ 0 at hp
    change (66 : ZMod 83)-1 ≠ 0 at ha
    change (66 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((66 : ZMod 83)+1)) at hr
    change IsSquare (3-(66 : ZMod 83)) at hs
    change 83=7 → (66 : ZMod 83) ≠ 3 at h7
    change 83=11 → (66 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (67 : ZMod 83)
    change (67 : ZMod 83) ≠ 0 at hp
    change (67 : ZMod 83)-1 ≠ 0 at ha
    change (67 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((67 : ZMod 83)+1)) at hr
    change IsSquare (3-(67 : ZMod 83)) at hs
    change 83=7 → (67 : ZMod 83) ≠ 3 at h7
    change 83=11 → (67 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (53 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (68 : ZMod 83)
    change (68 : ZMod 83) ≠ 0 at hp
    change (68 : ZMod 83)-1 ≠ 0 at ha
    change (68 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((68 : ZMod 83)+1)) at hr
    change IsSquare (3-(68 : ZMod 83)) at hs
    change 83=7 → (68 : ZMod 83) ≠ 3 at h7
    change 83=11 → (68 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (55 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (69 : ZMod 83)
    change (69 : ZMod 83) ≠ 0 at hp
    change (69 : ZMod 83)-1 ≠ 0 at ha
    change (69 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((69 : ZMod 83)+1)) at hr
    change IsSquare (3-(69 : ZMod 83)) at hs
    change 83=7 → (69 : ZMod 83) ≠ 3 at h7
    change 83=11 → (69 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (57 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (70 : ZMod 83)
    change (70 : ZMod 83) ≠ 0 at hp
    change (70 : ZMod 83)-1 ≠ 0 at ha
    change (70 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((70 : ZMod 83)+1)) at hr
    change IsSquare (3-(70 : ZMod 83)) at hs
    change 83=7 → (70 : ZMod 83) ≠ 3 at h7
    change 83=11 → (70 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨3,![25,39,30,19],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (71 : ZMod 83)
    change (71 : ZMod 83) ≠ 0 at hp
    change (71 : ZMod 83)-1 ≠ 0 at ha
    change (71 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((71 : ZMod 83)+1)) at hr
    change IsSquare (3-(71 : ZMod 83)) at hs
    change 83=7 → (71 : ZMod 83) ≠ 3 at h7
    change 83=11 → (71 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (72 : ZMod 83)
    change (72 : ZMod 83) ≠ 0 at hp
    change (72 : ZMod 83)-1 ≠ 0 at ha
    change (72 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((72 : ZMod 83)+1)) at hr
    change IsSquare (3-(72 : ZMod 83)) at hs
    change 83=7 → (72 : ZMod 83) ≠ 3 at h7
    change 83=11 → (72 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (73 : ZMod 83)
    change (73 : ZMod 83) ≠ 0 at hp
    change (73 : ZMod 83)-1 ≠ 0 at ha
    change (73 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((73 : ZMod 83)+1)) at hr
    change IsSquare (3-(73 : ZMod 83)) at hs
    change 83=7 → (73 : ZMod 83) ≠ 3 at h7
    change 83=11 → (73 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (74 : ZMod 83)
    change (74 : ZMod 83) ≠ 0 at hp
    change (74 : ZMod 83)-1 ≠ 0 at ha
    change (74 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((74 : ZMod 83)+1)) at hr
    change IsSquare (3-(74 : ZMod 83)) at hs
    change 83=7 → (74 : ZMod 83) ≠ 3 at h7
    change 83=11 → (74 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (67 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (75 : ZMod 83)
    change (75 : ZMod 83) ≠ 0 at hp
    change (75 : ZMod 83)-1 ≠ 0 at ha
    change (75 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((75 : ZMod 83)+1)) at hr
    change IsSquare (3-(75 : ZMod 83)) at hs
    change 83=7 → (75 : ZMod 83) ≠ 3 at h7
    change 83=11 → (75 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨10,![13,2,26,22],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (76 : ZMod 83)
    change (76 : ZMod 83) ≠ 0 at hp
    change (76 : ZMod 83)-1 ≠ 0 at ha
    change (76 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((76 : ZMod 83)+1)) at hr
    change IsSquare (3-(76 : ZMod 83)) at hs
    change 83=7 → (76 : ZMod 83) ≠ 3 at h7
    change 83=11 → (76 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (71 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (77 : ZMod 83)
    change (77 : ZMod 83) ≠ 0 at hp
    change (77 : ZMod 83)-1 ≠ 0 at ha
    change (77 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((77 : ZMod 83)+1)) at hr
    change IsSquare (3-(77 : ZMod 83)) at hs
    change 83=7 → (77 : ZMod 83) ≠ 3 at h7
    change 83=11 → (77 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (73 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (78 : ZMod 83)
    change (78 : ZMod 83) ≠ 0 at hp
    change (78 : ZMod 83)-1 ≠ 0 at ha
    change (78 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((78 : ZMod 83)+1)) at hr
    change IsSquare (3-(78 : ZMod 83)) at hs
    change 83=7 → (78 : ZMod 83) ≠ 3 at h7
    change 83=11 → (78 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (8 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (79 : ZMod 83)
    change (79 : ZMod 83) ≠ 0 at hp
    change (79 : ZMod 83)-1 ≠ 0 at ha
    change (79 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((79 : ZMod 83)+1)) at hr
    change IsSquare (3-(79 : ZMod 83)) at hs
    change 83=7 → (79 : ZMod 83) ≠ 3 at h7
    change 83=11 → (79 : ZMod 83) ≠ 5 at h11
    apply Or.inl
    refine ⟨20,![13,15,17,35],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (80 : ZMod 83)
    change (80 : ZMod 83) ≠ 0 at hp
    change (80 : ZMod 83)-1 ≠ 0 at ha
    change (80 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((80 : ZMod 83)+1)) at hr
    change IsSquare (3-(80 : ZMod 83)) at hs
    change 83=7 → (80 : ZMod 83) ≠ 3 at h7
    change 83=11 → (80 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (79 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (81 : ZMod 83)
    change (81 : ZMod 83) ≠ 0 at hp
    change (81 : ZMod 83)-1 ≠ 0 at ha
    change (81 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((81 : ZMod 83)+1)) at hr
    change IsSquare (3-(81 : ZMod 83)) at hs
    change 83=7 → (81 : ZMod 83) ≠ 3 at h7
    change 83=11 → (81 : ZMod 83) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 83) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (82 : ZMod 83)
    change (82 : ZMod 83) ≠ 0 at hp
    change (82 : ZMod 83)-1 ≠ 0 at ha
    change (82 : ZMod 83)+1 ≠ 0 at hb
    change IsSquare (2*((82 : ZMod 83)+1)) at hr
    change IsSquare (3-(82 : ZMod 83)) at hs
    change 83=7 → (82 : ZMod 83) ≠ 3 at h7
    change 83=11 → (82 : ZMod 83) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts83

private instance prime89 : Fact (Nat.Prime 89) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts89 (p : ZMod 89) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 89=7 → p ≠ 3) (h11 : 89=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 89)
    change (0 : ZMod 89) ≠ 0 at hp
    change (0 : ZMod 89)-1 ≠ 0 at ha
    change (0 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 89)+1)) at hr
    change IsSquare (3-(0 : ZMod 89)) at hs
    change 89=7 → (0 : ZMod 89) ≠ 3 at h7
    change 89=11 → (0 : ZMod 89) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 89)
    change (1 : ZMod 89) ≠ 0 at hp
    change (1 : ZMod 89)-1 ≠ 0 at ha
    change (1 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 89)+1)) at hr
    change IsSquare (3-(1 : ZMod 89)) at hs
    change 89=7 → (1 : ZMod 89) ≠ 3 at h7
    change 89=11 → (1 : ZMod 89) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 89)
    change (2 : ZMod 89) ≠ 0 at hp
    change (2 : ZMod 89)-1 ≠ 0 at ha
    change (2 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 89)+1)) at hr
    change IsSquare (3-(2 : ZMod 89)) at hs
    change 89=7 → (2 : ZMod 89) ≠ 3 at h7
    change 89=11 → (2 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (3 : ZMod 89)
    change (3 : ZMod 89) ≠ 0 at hp
    change (3 : ZMod 89)-1 ≠ 0 at ha
    change (3 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 89)+1)) at hr
    change IsSquare (3-(3 : ZMod 89)) at hs
    change 89=7 → (3 : ZMod 89) ≠ 3 at h7
    change 89=11 → (3 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,21,39,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (4 : ZMod 89)
    change (4 : ZMod 89) ≠ 0 at hp
    change (4 : ZMod 89)-1 ≠ 0 at ha
    change (4 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 89)+1)) at hr
    change IsSquare (3-(4 : ZMod 89)) at hs
    change 89=7 → (4 : ZMod 89) ≠ 3 at h7
    change 89=11 → (4 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![2,0,38,39],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (5 : ZMod 89)
    change (5 : ZMod 89) ≠ 0 at hp
    change (5 : ZMod 89)-1 ≠ 0 at ha
    change (5 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 89)+1)) at hr
    change IsSquare (3-(5 : ZMod 89)) at hs
    change 89=7 → (5 : ZMod 89) ≠ 3 at h7
    change 89=11 → (5 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (6 : ZMod 89)
    change (6 : ZMod 89) ≠ 0 at hp
    change (6 : ZMod 89)-1 ≠ 0 at ha
    change (6 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 89)+1)) at hr
    change IsSquare (3-(6 : ZMod 89)) at hs
    change 89=7 → (6 : ZMod 89) ≠ 3 at h7
    change 89=11 → (6 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 89)
    change (7 : ZMod 89) ≠ 0 at hp
    change (7 : ZMod 89)-1 ≠ 0 at ha
    change (7 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 89)+1)) at hr
    change IsSquare (3-(7 : ZMod 89)) at hs
    change 89=7 → (7 : ZMod 89) ≠ 3 at h7
    change 89=11 → (7 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨7,![7,28,22,36],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (8 : ZMod 89)
    change (8 : ZMod 89) ≠ 0 at hp
    change (8 : ZMod 89)-1 ≠ 0 at ha
    change (8 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 89)+1)) at hr
    change IsSquare (3-(8 : ZMod 89)) at hs
    change 89=7 → (8 : ZMod 89) ≠ 3 at h7
    change 89=11 → (8 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![39,0,6,4],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (9 : ZMod 89)
    change (9 : ZMod 89) ≠ 0 at hp
    change (9 : ZMod 89)-1 ≠ 0 at ha
    change (9 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 89)+1)) at hr
    change IsSquare (3-(9 : ZMod 89)) at hs
    change 89=7 → (9 : ZMod 89) ≠ 3 at h7
    change 89=11 → (9 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (83 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (10 : ZMod 89)
    change (10 : ZMod 89) ≠ 0 at hp
    change (10 : ZMod 89)-1 ≠ 0 at ha
    change (10 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 89)+1)) at hr
    change IsSquare (3-(10 : ZMod 89)) at hs
    change 89=7 → (10 : ZMod 89) ≠ 3 at h7
    change 89=11 → (10 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (82 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (11 : ZMod 89)
    change (11 : ZMod 89) ≠ 0 at hp
    change (11 : ZMod 89)-1 ≠ 0 at ha
    change (11 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 89)+1)) at hr
    change IsSquare (3-(11 : ZMod 89)) at hs
    change 89=7 → (11 : ZMod 89) ≠ 3 at h7
    change 89=11 → (11 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (12 : ZMod 89)
    change (12 : ZMod 89) ≠ 0 at hp
    change (12 : ZMod 89)-1 ≠ 0 at ha
    change (12 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 89)+1)) at hr
    change IsSquare (3-(12 : ZMod 89)) at hs
    change 89=7 → (12 : ZMod 89) ≠ 3 at h7
    change 89=11 → (12 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (13 : ZMod 89)
    change (13 : ZMod 89) ≠ 0 at hp
    change (13 : ZMod 89)-1 ≠ 0 at ha
    change (13 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 89)+1)) at hr
    change IsSquare (3-(13 : ZMod 89)) at hs
    change 89=7 → (13 : ZMod 89) ≠ 3 at h7
    change 89=11 → (13 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (14 : ZMod 89)
    change (14 : ZMod 89) ≠ 0 at hp
    change (14 : ZMod 89)-1 ≠ 0 at ha
    change (14 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 89)+1)) at hr
    change IsSquare (3-(14 : ZMod 89)) at hs
    change 89=7 → (14 : ZMod 89) ≠ 3 at h7
    change 89=11 → (14 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 89)
    change (15 : ZMod 89) ≠ 0 at hp
    change (15 : ZMod 89)-1 ≠ 0 at ha
    change (15 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 89)+1)) at hr
    change IsSquare (3-(15 : ZMod 89)) at hs
    change 89=7 → (15 : ZMod 89) ≠ 3 at h7
    change 89=11 → (15 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (77 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (16 : ZMod 89)
    change (16 : ZMod 89) ≠ 0 at hp
    change (16 : ZMod 89)-1 ≠ 0 at ha
    change (16 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 89)+1)) at hr
    change IsSquare (3-(16 : ZMod 89)) at hs
    change 89=7 → (16 : ZMod 89) ≠ 3 at h7
    change 89=11 → (16 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (76 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (17 : ZMod 89)
    change (17 : ZMod 89) ≠ 0 at hp
    change (17 : ZMod 89)-1 ≠ 0 at ha
    change (17 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 89)+1)) at hr
    change IsSquare (3-(17 : ZMod 89)) at hs
    change 89=7 → (17 : ZMod 89) ≠ 3 at h7
    change 89=11 → (17 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (75 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (18 : ZMod 89)
    change (18 : ZMod 89) ≠ 0 at hp
    change (18 : ZMod 89)-1 ≠ 0 at ha
    change (18 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 89)+1)) at hr
    change IsSquare (3-(18 : ZMod 89)) at hs
    change 89=7 → (18 : ZMod 89) ≠ 3 at h7
    change 89=11 → (18 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (38 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (19 : ZMod 89)
    change (19 : ZMod 89) ≠ 0 at hp
    change (19 : ZMod 89)-1 ≠ 0 at ha
    change (19 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 89)+1)) at hr
    change IsSquare (3-(19 : ZMod 89)) at hs
    change 89=7 → (19 : ZMod 89) ≠ 3 at h7
    change 89=11 → (19 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,26,29,38],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (20 : ZMod 89)
    change (20 : ZMod 89) ≠ 0 at hp
    change (20 : ZMod 89)-1 ≠ 0 at ha
    change (20 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 89)+1)) at hr
    change IsSquare (3-(20 : ZMod 89)) at hs
    change 89=7 → (20 : ZMod 89) ≠ 3 at h7
    change 89=11 → (20 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![38,0,23,29],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (21 : ZMod 89)
    change (21 : ZMod 89) ≠ 0 at hp
    change (21 : ZMod 89)-1 ≠ 0 at ha
    change (21 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 89)+1)) at hr
    change IsSquare (3-(21 : ZMod 89)) at hs
    change 89=7 → (21 : ZMod 89) ≠ 3 at h7
    change 89=11 → (21 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,7,20,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (22 : ZMod 89)
    change (22 : ZMod 89) ≠ 0 at hp
    change (22 : ZMod 89)-1 ≠ 0 at ha
    change (22 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 89)+1)) at hr
    change IsSquare (3-(22 : ZMod 89)) at hs
    change 89=7 → (22 : ZMod 89) ≠ 3 at h7
    change 89=11 → (22 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (46 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (23 : ZMod 89)
    change (23 : ZMod 89) ≠ 0 at hp
    change (23 : ZMod 89)-1 ≠ 0 at ha
    change (23 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 89)+1)) at hr
    change IsSquare (3-(23 : ZMod 89)) at hs
    change 89=7 → (23 : ZMod 89) ≠ 3 at h7
    change 89=11 → (23 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (48 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (24 : ZMod 89)
    change (24 : ZMod 89) ≠ 0 at hp
    change (24 : ZMod 89)-1 ≠ 0 at ha
    change (24 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 89)+1)) at hr
    change IsSquare (3-(24 : ZMod 89)) at hs
    change 89=7 → (24 : ZMod 89) ≠ 3 at h7
    change 89=11 → (24 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨7,![41,3,20,39],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (25 : ZMod 89)
    change (25 : ZMod 89) ≠ 0 at hp
    change (25 : ZMod 89)-1 ≠ 0 at ha
    change (25 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 89)+1)) at hr
    change IsSquare (3-(25 : ZMod 89)) at hs
    change 89=7 → (25 : ZMod 89) ≠ 3 at h7
    change 89=11 → (25 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (52 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (26 : ZMod 89)
    change (26 : ZMod 89) ≠ 0 at hp
    change (26 : ZMod 89)-1 ≠ 0 at ha
    change (26 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 89)+1)) at hr
    change IsSquare (3-(26 : ZMod 89)) at hs
    change 89=7 → (26 : ZMod 89) ≠ 3 at h7
    change 89=11 → (26 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (54 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (27 : ZMod 89)
    change (27 : ZMod 89) ≠ 0 at hp
    change (27 : ZMod 89)-1 ≠ 0 at ha
    change (27 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 89)+1)) at hr
    change IsSquare (3-(27 : ZMod 89)) at hs
    change 89=7 → (27 : ZMod 89) ≠ 3 at h7
    change 89=11 → (27 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (56 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (28 : ZMod 89)
    change (28 : ZMod 89) ≠ 0 at hp
    change (28 : ZMod 89)-1 ≠ 0 at ha
    change (28 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 89)+1)) at hr
    change IsSquare (3-(28 : ZMod 89)) at hs
    change 89=7 → (28 : ZMod 89) ≠ 3 at h7
    change 89=11 → (28 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (58 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (29 : ZMod 89)
    change (29 : ZMod 89) ≠ 0 at hp
    change (29 : ZMod 89)-1 ≠ 0 at ha
    change (29 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 89)+1)) at hr
    change IsSquare (3-(29 : ZMod 89)) at hs
    change 89=7 → (29 : ZMod 89) ≠ 3 at h7
    change 89=11 → (29 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (60 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (30 : ZMod 89)
    change (30 : ZMod 89) ≠ 0 at hp
    change (30 : ZMod 89)-1 ≠ 0 at ha
    change (30 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 89)+1)) at hr
    change IsSquare (3-(30 : ZMod 89)) at hs
    change 89=7 → (30 : ZMod 89) ≠ 3 at h7
    change 89=11 → (30 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (62 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (31 : ZMod 89)
    change (31 : ZMod 89) ≠ 0 at hp
    change (31 : ZMod 89)-1 ≠ 0 at ha
    change (31 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 89)+1)) at hr
    change IsSquare (3-(31 : ZMod 89)) at hs
    change 89=7 → (31 : ZMod 89) ≠ 3 at h7
    change 89=11 → (31 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (61 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (32 : ZMod 89)
    change (32 : ZMod 89) ≠ 0 at hp
    change (32 : ZMod 89)-1 ≠ 0 at ha
    change (32 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 89)+1)) at hr
    change IsSquare (3-(32 : ZMod 89)) at hs
    change 89=7 → (32 : ZMod 89) ≠ 3 at h7
    change 89=11 → (32 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (66 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (33 : ZMod 89)
    change (33 : ZMod 89) ≠ 0 at hp
    change (33 : ZMod 89)-1 ≠ 0 at ha
    change (33 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 89)+1)) at hr
    change IsSquare (3-(33 : ZMod 89)) at hs
    change 89=7 → (33 : ZMod 89) ≠ 3 at h7
    change 89=11 → (33 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (59 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (34 : ZMod 89)
    change (34 : ZMod 89) ≠ 0 at hp
    change (34 : ZMod 89)-1 ≠ 0 at ha
    change (34 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 89)+1)) at hr
    change IsSquare (3-(34 : ZMod 89)) at hs
    change 89=7 → (34 : ZMod 89) ≠ 3 at h7
    change 89=11 → (34 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (70 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (35 : ZMod 89)
    change (35 : ZMod 89) ≠ 0 at hp
    change (35 : ZMod 89)-1 ≠ 0 at ha
    change (35 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 89)+1)) at hr
    change IsSquare (3-(35 : ZMod 89)) at hs
    change 89=7 → (35 : ZMod 89) ≠ 3 at h7
    change 89=11 → (35 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,33,28,6],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (36 : ZMod 89)
    change (36 : ZMod 89) ≠ 0 at hp
    change (36 : ZMod 89)-1 ≠ 0 at ha
    change (36 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 89)+1)) at hr
    change IsSquare (3-(36 : ZMod 89)) at hs
    change 89=7 → (36 : ZMod 89) ≠ 3 at h7
    change 89=11 → (36 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (74 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (37 : ZMod 89)
    change (37 : ZMod 89) ≠ 0 at hp
    change (37 : ZMod 89)-1 ≠ 0 at ha
    change (37 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 89)+1)) at hr
    change IsSquare (3-(37 : ZMod 89)) at hs
    change 89=7 → (37 : ZMod 89) ≠ 3 at h7
    change 89=11 → (37 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (76 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (38 : ZMod 89)
    change (38 : ZMod 89) ≠ 0 at hp
    change (38 : ZMod 89)-1 ≠ 0 at ha
    change (38 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 89)+1)) at hr
    change IsSquare (3-(38 : ZMod 89)) at hs
    change 89=7 → (38 : ZMod 89) ≠ 3 at h7
    change 89=11 → (38 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (54 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (39 : ZMod 89)
    change (39 : ZMod 89) ≠ 0 at hp
    change (39 : ZMod 89)-1 ≠ 0 at ha
    change (39 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 89)+1)) at hr
    change IsSquare (3-(39 : ZMod 89)) at hs
    change 89=7 → (39 : ZMod 89) ≠ 3 at h7
    change 89=11 → (39 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![22,0,31,16],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (40 : ZMod 89)
    change (40 : ZMod 89) ≠ 0 at hp
    change (40 : ZMod 89)-1 ≠ 0 at ha
    change (40 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 89)+1)) at hr
    change IsSquare (3-(40 : ZMod 89)) at hs
    change 89=7 → (40 : ZMod 89) ≠ 3 at h7
    change 89=11 → (40 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (82 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (41 : ZMod 89)
    change (41 : ZMod 89) ≠ 0 at hp
    change (41 : ZMod 89)-1 ≠ 0 at ha
    change (41 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 89)+1)) at hr
    change IsSquare (3-(41 : ZMod 89)) at hs
    change 89=7 → (41 : ZMod 89) ≠ 3 at h7
    change 89=11 → (41 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (51 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (42 : ZMod 89)
    change (42 : ZMod 89) ≠ 0 at hp
    change (42 : ZMod 89)-1 ≠ 0 at ha
    change (42 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 89)+1)) at hr
    change IsSquare (3-(42 : ZMod 89)) at hs
    change 89=7 → (42 : ZMod 89) ≠ 3 at h7
    change 89=11 → (42 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (86 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (43 : ZMod 89)
    change (43 : ZMod 89) ≠ 0 at hp
    change (43 : ZMod 89)-1 ≠ 0 at ha
    change (43 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((43 : ZMod 89)+1)) at hr
    change IsSquare (3-(43 : ZMod 89)) at hs
    change 89=7 → (43 : ZMod 89) ≠ 3 at h7
    change 89=11 → (43 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,19,34,20],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (44 : ZMod 89)
    change (44 : ZMod 89) ≠ 0 at hp
    change (44 : ZMod 89)-1 ≠ 0 at ha
    change (44 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((44 : ZMod 89)+1)) at hr
    change IsSquare (3-(44 : ZMod 89)) at hs
    change 89=7 → (44 : ZMod 89) ≠ 3 at h7
    change 89=11 → (44 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (48 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (45 : ZMod 89)
    change (45 : ZMod 89) ≠ 0 at hp
    change (45 : ZMod 89)-1 ≠ 0 at ha
    change (45 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((45 : ZMod 89)+1)) at hr
    change IsSquare (3-(45 : ZMod 89)) at hs
    change 89=7 → (45 : ZMod 89) ≠ 3 at h7
    change 89=11 → (45 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (3 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (46 : ZMod 89)
    change (46 : ZMod 89) ≠ 0 at hp
    change (46 : ZMod 89)-1 ≠ 0 at ha
    change (46 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((46 : ZMod 89)+1)) at hr
    change IsSquare (3-(46 : ZMod 89)) at hs
    change 89=7 → (46 : ZMod 89) ≠ 3 at h7
    change 89=11 → (46 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (46 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (47 : ZMod 89)
    change (47 : ZMod 89) ≠ 0 at hp
    change (47 : ZMod 89)-1 ≠ 0 at ha
    change (47 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((47 : ZMod 89)+1)) at hr
    change IsSquare (3-(47 : ZMod 89)) at hs
    change 89=7 → (47 : ZMod 89) ≠ 3 at h7
    change 89=11 → (47 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (48 : ZMod 89)
    change (48 : ZMod 89) ≠ 0 at hp
    change (48 : ZMod 89)-1 ≠ 0 at ha
    change (48 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((48 : ZMod 89)+1)) at hr
    change IsSquare (3-(48 : ZMod 89)) at hs
    change 89=7 → (48 : ZMod 89) ≠ 3 at h7
    change 89=11 → (48 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,23,3,7],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (49 : ZMod 89)
    change (49 : ZMod 89) ≠ 0 at hp
    change (49 : ZMod 89)-1 ≠ 0 at ha
    change (49 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((49 : ZMod 89)+1)) at hr
    change IsSquare (3-(49 : ZMod 89)) at hs
    change 89=7 → (49 : ZMod 89) ≠ 3 at h7
    change 89=11 → (49 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (50 : ZMod 89)
    change (50 : ZMod 89) ≠ 0 at hp
    change (50 : ZMod 89)-1 ≠ 0 at ha
    change (50 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((50 : ZMod 89)+1)) at hr
    change IsSquare (3-(50 : ZMod 89)) at hs
    change 89=7 → (50 : ZMod 89) ≠ 3 at h7
    change 89=11 → (50 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (51 : ZMod 89)
    change (51 : ZMod 89) ≠ 0 at hp
    change (51 : ZMod 89)-1 ≠ 0 at ha
    change (51 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((51 : ZMod 89)+1)) at hr
    change IsSquare (3-(51 : ZMod 89)) at hs
    change 89=7 → (51 : ZMod 89) ≠ 3 at h7
    change 89=11 → (51 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (52 : ZMod 89)
    change (52 : ZMod 89) ≠ 0 at hp
    change (52 : ZMod 89)-1 ≠ 0 at ha
    change (52 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((52 : ZMod 89)+1)) at hr
    change IsSquare (3-(52 : ZMod 89)) at hs
    change 89=7 → (52 : ZMod 89) ≠ 3 at h7
    change 89=11 → (52 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![35,2,19,27],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (53 : ZMod 89)
    change (53 : ZMod 89) ≠ 0 at hp
    change (53 : ZMod 89)-1 ≠ 0 at ha
    change (53 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((53 : ZMod 89)+1)) at hr
    change IsSquare (3-(53 : ZMod 89)) at hs
    change 89=7 → (53 : ZMod 89) ≠ 3 at h7
    change 89=11 → (53 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (54 : ZMod 89)
    change (54 : ZMod 89) ≠ 0 at hp
    change (54 : ZMod 89)-1 ≠ 0 at ha
    change (54 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((54 : ZMod 89)+1)) at hr
    change IsSquare (3-(54 : ZMod 89)) at hs
    change 89=7 → (54 : ZMod 89) ≠ 3 at h7
    change 89=11 → (54 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (38 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (55 : ZMod 89)
    change (55 : ZMod 89) ≠ 0 at hp
    change (55 : ZMod 89)-1 ≠ 0 at ha
    change (55 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((55 : ZMod 89)+1)) at hr
    change IsSquare (3-(55 : ZMod 89)) at hs
    change 89=7 → (55 : ZMod 89) ≠ 3 at h7
    change 89=11 → (55 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (56 : ZMod 89)
    change (56 : ZMod 89) ≠ 0 at hp
    change (56 : ZMod 89)-1 ≠ 0 at ha
    change (56 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((56 : ZMod 89)+1)) at hr
    change IsSquare (3-(56 : ZMod 89)) at hs
    change 89=7 → (56 : ZMod 89) ≠ 3 at h7
    change 89=11 → (56 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,35,5,18],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (57 : ZMod 89)
    change (57 : ZMod 89) ≠ 0 at hp
    change (57 : ZMod 89)-1 ≠ 0 at ha
    change (57 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((57 : ZMod 89)+1)) at hr
    change IsSquare (3-(57 : ZMod 89)) at hs
    change 89=7 → (57 : ZMod 89) ≠ 3 at h7
    change 89=11 → (57 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (27 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (58 : ZMod 89)
    change (58 : ZMod 89) ≠ 0 at hp
    change (58 : ZMod 89)-1 ≠ 0 at ha
    change (58 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((58 : ZMod 89)+1)) at hr
    change IsSquare (3-(58 : ZMod 89)) at hs
    change 89=7 → (58 : ZMod 89) ≠ 3 at h7
    change 89=11 → (58 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (59 : ZMod 89)
    change (59 : ZMod 89) ≠ 0 at hp
    change (59 : ZMod 89)-1 ≠ 0 at ha
    change (59 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((59 : ZMod 89)+1)) at hr
    change IsSquare (3-(59 : ZMod 89)) at hs
    change 89=7 → (59 : ZMod 89) ≠ 3 at h7
    change 89=11 → (59 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (31 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (60 : ZMod 89)
    change (60 : ZMod 89) ≠ 0 at hp
    change (60 : ZMod 89)-1 ≠ 0 at ha
    change (60 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((60 : ZMod 89)+1)) at hr
    change IsSquare (3-(60 : ZMod 89)) at hs
    change 89=7 → (60 : ZMod 89) ≠ 3 at h7
    change 89=11 → (60 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (33 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (61 : ZMod 89)
    change (61 : ZMod 89) ≠ 0 at hp
    change (61 : ZMod 89)-1 ≠ 0 at ha
    change (61 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((61 : ZMod 89)+1)) at hr
    change IsSquare (3-(61 : ZMod 89)) at hs
    change 89=7 → (61 : ZMod 89) ≠ 3 at h7
    change 89=11 → (61 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (35 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (62 : ZMod 89)
    change (62 : ZMod 89) ≠ 0 at hp
    change (62 : ZMod 89)-1 ≠ 0 at ha
    change (62 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((62 : ZMod 89)+1)) at hr
    change IsSquare (3-(62 : ZMod 89)) at hs
    change 89=7 → (62 : ZMod 89) ≠ 3 at h7
    change 89=11 → (62 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (37 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (63 : ZMod 89)
    change (63 : ZMod 89) ≠ 0 at hp
    change (63 : ZMod 89)-1 ≠ 0 at ha
    change (63 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((63 : ZMod 89)+1)) at hr
    change IsSquare (3-(63 : ZMod 89)) at hs
    change 89=7 → (63 : ZMod 89) ≠ 3 at h7
    change 89=11 → (63 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (64 : ZMod 89)
    change (64 : ZMod 89) ≠ 0 at hp
    change (64 : ZMod 89)-1 ≠ 0 at ha
    change (64 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((64 : ZMod 89)+1)) at hr
    change IsSquare (3-(64 : ZMod 89)) at hs
    change 89=7 → (64 : ZMod 89) ≠ 3 at h7
    change 89=11 → (64 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (41 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (65 : ZMod 89)
    change (65 : ZMod 89) ≠ 0 at hp
    change (65 : ZMod 89)-1 ≠ 0 at ha
    change (65 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((65 : ZMod 89)+1)) at hr
    change IsSquare (3-(65 : ZMod 89)) at hs
    change 89=7 → (65 : ZMod 89) ≠ 3 at h7
    change 89=11 → (65 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (43 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (66 : ZMod 89)
    change (66 : ZMod 89) ≠ 0 at hp
    change (66 : ZMod 89)-1 ≠ 0 at ha
    change (66 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((66 : ZMod 89)+1)) at hr
    change IsSquare (3-(66 : ZMod 89)) at hs
    change 89=7 → (66 : ZMod 89) ≠ 3 at h7
    change 89=11 → (66 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (67 : ZMod 89)
    change (67 : ZMod 89) ≠ 0 at hp
    change (67 : ZMod 89)-1 ≠ 0 at ha
    change (67 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((67 : ZMod 89)+1)) at hr
    change IsSquare (3-(67 : ZMod 89)) at hs
    change 89=7 → (67 : ZMod 89) ≠ 3 at h7
    change 89=11 → (67 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![44,0,19,32],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (68 : ZMod 89)
    change (68 : ZMod 89) ≠ 0 at hp
    change (68 : ZMod 89)-1 ≠ 0 at ha
    change (68 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((68 : ZMod 89)+1)) at hr
    change IsSquare (3-(68 : ZMod 89)) at hs
    change 89=7 → (68 : ZMod 89) ≠ 3 at h7
    change 89=11 → (68 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (24 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (69 : ZMod 89)
    change (69 : ZMod 89) ≠ 0 at hp
    change (69 : ZMod 89)-1 ≠ 0 at ha
    change (69 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((69 : ZMod 89)+1)) at hr
    change IsSquare (3-(69 : ZMod 89)) at hs
    change 89=7 → (69 : ZMod 89) ≠ 3 at h7
    change 89=11 → (69 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (51 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (70 : ZMod 89)
    change (70 : ZMod 89) ≠ 0 at hp
    change (70 : ZMod 89)-1 ≠ 0 at ha
    change (70 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((70 : ZMod 89)+1)) at hr
    change IsSquare (3-(70 : ZMod 89)) at hs
    change 89=7 → (70 : ZMod 89) ≠ 3 at h7
    change 89=11 → (70 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,29,26,31],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (71 : ZMod 89)
    change (71 : ZMod 89) ≠ 0 at hp
    change (71 : ZMod 89)-1 ≠ 0 at ha
    change (71 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((71 : ZMod 89)+1)) at hr
    change IsSquare (3-(71 : ZMod 89)) at hs
    change 89=7 → (71 : ZMod 89) ≠ 3 at h7
    change 89=11 → (71 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![31,0,33,26],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (72 : ZMod 89)
    change (72 : ZMod 89) ≠ 0 at hp
    change (72 : ZMod 89)-1 ≠ 0 at ha
    change (72 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((72 : ZMod 89)+1)) at hr
    change IsSquare (3-(72 : ZMod 89)) at hs
    change 89=7 → (72 : ZMod 89) ≠ 3 at h7
    change 89=11 → (72 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,6,18,42],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (73 : ZMod 89)
    change (73 : ZMod 89) ≠ 0 at hp
    change (73 : ZMod 89)-1 ≠ 0 at ha
    change (73 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((73 : ZMod 89)+1)) at hr
    change IsSquare (3-(73 : ZMod 89)) at hs
    change 89=7 → (73 : ZMod 89) ≠ 3 at h7
    change 89=11 → (73 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (59 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (74 : ZMod 89)
    change (74 : ZMod 89) ≠ 0 at hp
    change (74 : ZMod 89)-1 ≠ 0 at ha
    change (74 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((74 : ZMod 89)+1)) at hr
    change IsSquare (3-(74 : ZMod 89)) at hs
    change 89=7 → (74 : ZMod 89) ≠ 3 at h7
    change 89=11 → (74 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (61 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (75 : ZMod 89)
    change (75 : ZMod 89) ≠ 0 at hp
    change (75 : ZMod 89)-1 ≠ 0 at ha
    change (75 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((75 : ZMod 89)+1)) at hr
    change IsSquare (3-(75 : ZMod 89)) at hs
    change 89=7 → (75 : ZMod 89) ≠ 3 at h7
    change 89=11 → (75 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (63 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (76 : ZMod 89)
    change (76 : ZMod 89) ≠ 0 at hp
    change (76 : ZMod 89)-1 ≠ 0 at ha
    change (76 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((76 : ZMod 89)+1)) at hr
    change IsSquare (3-(76 : ZMod 89)) at hs
    change 89=7 → (76 : ZMod 89) ≠ 3 at h7
    change 89=11 → (76 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (65 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (77 : ZMod 89)
    change (77 : ZMod 89) ≠ 0 at hp
    change (77 : ZMod 89)-1 ≠ 0 at ha
    change (77 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((77 : ZMod 89)+1)) at hr
    change IsSquare (3-(77 : ZMod 89)) at hs
    change 89=7 → (77 : ZMod 89) ≠ 3 at h7
    change 89=11 → (77 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (78 : ZMod 89)
    change (78 : ZMod 89) ≠ 0 at hp
    change (78 : ZMod 89)-1 ≠ 0 at ha
    change (78 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((78 : ZMod 89)+1)) at hr
    change IsSquare (3-(78 : ZMod 89)) at hs
    change 89=7 → (78 : ZMod 89) ≠ 3 at h7
    change 89=11 → (78 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (79 : ZMod 89)
    change (79 : ZMod 89) ≠ 0 at hp
    change (79 : ZMod 89)-1 ≠ 0 at ha
    change (79 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((79 : ZMod 89)+1)) at hr
    change IsSquare (3-(79 : ZMod 89)) at hs
    change 89=7 → (79 : ZMod 89) ≠ 3 at h7
    change 89=11 → (79 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (80 : ZMod 89)
    change (80 : ZMod 89) ≠ 0 at hp
    change (80 : ZMod 89)-1 ≠ 0 at ha
    change (80 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((80 : ZMod 89)+1)) at hr
    change IsSquare (3-(80 : ZMod 89)) at hs
    change 89=7 → (80 : ZMod 89) ≠ 3 at h7
    change 89=11 → (80 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (12 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (81 : ZMod 89)
    change (81 : ZMod 89) ≠ 0 at hp
    change (81 : ZMod 89)-1 ≠ 0 at ha
    change (81 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((81 : ZMod 89)+1)) at hr
    change IsSquare (3-(81 : ZMod 89)) at hs
    change 89=7 → (81 : ZMod 89) ≠ 3 at h7
    change 89=11 → (81 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (75 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (82 : ZMod 89)
    change (82 : ZMod 89) ≠ 0 at hp
    change (82 : ZMod 89)-1 ≠ 0 at ha
    change (82 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((82 : ZMod 89)+1)) at hr
    change IsSquare (3-(82 : ZMod 89)) at hs
    change 89=7 → (82 : ZMod 89) ≠ 3 at h7
    change 89=11 → (82 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (77 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (83 : ZMod 89)
    change (83 : ZMod 89) ≠ 0 at hp
    change (83 : ZMod 89)-1 ≠ 0 at ha
    change (83 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((83 : ZMod 89)+1)) at hr
    change IsSquare (3-(83 : ZMod 89)) at hs
    change 89=7 → (83 : ZMod 89) ≠ 3 at h7
    change 89=11 → (83 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![34,31,14,35],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (84 : ZMod 89)
    change (84 : ZMod 89) ≠ 0 at hp
    change (84 : ZMod 89)-1 ≠ 0 at ha
    change (84 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((84 : ZMod 89)+1)) at hr
    change IsSquare (3-(84 : ZMod 89)) at hs
    change 89=7 → (84 : ZMod 89) ≠ 3 at h7
    change 89=11 → (84 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![23,0,42,41],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (85 : ZMod 89)
    change (85 : ZMod 89) ≠ 0 at hp
    change (85 : ZMod 89)-1 ≠ 0 at ha
    change (85 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((85 : ZMod 89)+1)) at hr
    change IsSquare (3-(85 : ZMod 89)) at hs
    change 89=7 → (85 : ZMod 89) ≠ 3 at h7
    change 89=11 → (85 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (83 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (86 : ZMod 89)
    change (86 : ZMod 89) ≠ 0 at hp
    change (86 : ZMod 89)-1 ≠ 0 at ha
    change (86 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((86 : ZMod 89)+1)) at hr
    change IsSquare (3-(86 : ZMod 89)) at hs
    change 89=7 → (86 : ZMod 89) ≠ 3 at h7
    change 89=11 → (86 : ZMod 89) ≠ 5 at h11
    have hn : ¬IsSquare (6 : ZMod 89) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (87 : ZMod 89)
    change (87 : ZMod 89) ≠ 0 at hp
    change (87 : ZMod 89)-1 ≠ 0 at ha
    change (87 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((87 : ZMod 89)+1)) at hr
    change IsSquare (3-(87 : ZMod 89)) at hs
    change 89=7 → (87 : ZMod 89) ≠ 3 at h7
    change 89=11 → (87 : ZMod 89) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![40,0,21,21],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (88 : ZMod 89)
    change (88 : ZMod 89) ≠ 0 at hp
    change (88 : ZMod 89)-1 ≠ 0 at ha
    change (88 : ZMod 89)+1 ≠ 0 at hb
    change IsSquare (2*((88 : ZMod 89)+1)) at hr
    change IsSquare (3-(88 : ZMod 89)) at hs
    change 89=7 → (88 : ZMod 89) ≠ 3 at h7
    change 89=11 → (88 : ZMod 89) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts89

private instance prime97 : Fact (Nat.Prime 97) := ⟨by decide⟩

/-- Exhaustive exact finite residue check, with explicit root witnesses. -/
theorem charts97 (p : ZMod 97) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : 97=7 → p ≠ 3) (h11 : 97=11 → p ≠ 5) : Charts p := by
  fin_cases p
  · change Charts (0 : ZMod 97)
    change (0 : ZMod 97) ≠ 0 at hp
    change (0 : ZMod 97)-1 ≠ 0 at ha
    change (0 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((0 : ZMod 97)+1)) at hr
    change IsSquare (3-(0 : ZMod 97)) at hs
    change 97=7 → (0 : ZMod 97) ≠ 3 at h7
    change 97=11 → (0 : ZMod 97) ≠ 5 at h11
    exact False.elim (hp (by decide))
  · change Charts (1 : ZMod 97)
    change (1 : ZMod 97) ≠ 0 at hp
    change (1 : ZMod 97)-1 ≠ 0 at ha
    change (1 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((1 : ZMod 97)+1)) at hr
    change IsSquare (3-(1 : ZMod 97)) at hs
    change 97=7 → (1 : ZMod 97) ≠ 3 at h7
    change 97=11 → (1 : ZMod 97) ≠ 5 at h11
    exact False.elim (ha (by decide))
  · change Charts (2 : ZMod 97)
    change (2 : ZMod 97) ≠ 0 at hp
    change (2 : ZMod 97)-1 ≠ 0 at ha
    change (2 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((2 : ZMod 97)+1)) at hr
    change IsSquare (3-(2 : ZMod 97)) at hs
    change 97=7 → (2 : ZMod 97) ≠ 3 at h7
    change 97=11 → (2 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,17,43,10],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (3 : ZMod 97)
    change (3 : ZMod 97) ≠ 0 at hp
    change (3 : ZMod 97)-1 ≠ 0 at ha
    change (3 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((3 : ZMod 97)+1)) at hr
    change IsSquare (3-(3 : ZMod 97)) at hs
    change 97=7 → (3 : ZMod 97) ≠ 3 at h7
    change 97=11 → (3 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,44,28,2],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (4 : ZMod 97)
    change (4 : ZMod 97) ≠ 0 at hp
    change (4 : ZMod 97)-1 ≠ 0 at ha
    change (4 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((4 : ZMod 97)+1)) at hr
    change IsSquare (3-(4 : ZMod 97)) at hs
    change 97=7 → (4 : ZMod 97) ≠ 3 at h7
    change 97=11 → (4 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (5 : ZMod 97)
    change (5 : ZMod 97) ≠ 0 at hp
    change (5 : ZMod 97)-1 ≠ 0 at ha
    change (5 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((5 : ZMod 97)+1)) at hr
    change IsSquare (3-(5 : ZMod 97)) at hs
    change 97=7 → (5 : ZMod 97) ≠ 3 at h7
    change 97=11 → (5 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,34,20,43],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (6 : ZMod 97)
    change (6 : ZMod 97) ≠ 0 at hp
    change (6 : ZMod 97)-1 ≠ 0 at ha
    change (6 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((6 : ZMod 97)+1)) at hr
    change IsSquare (3-(6 : ZMod 97)) at hs
    change 97=7 → (6 : ZMod 97) ≠ 3 at h7
    change 97=11 → (6 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (14 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (7 : ZMod 97)
    change (7 : ZMod 97) ≠ 0 at hp
    change (7 : ZMod 97)-1 ≠ 0 at ha
    change (7 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((7 : ZMod 97)+1)) at hr
    change IsSquare (3-(7 : ZMod 97)) at hs
    change 97=7 → (7 : ZMod 97) ≠ 3 at h7
    change 97=11 → (7 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,45,4,28],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (8 : ZMod 97)
    change (8 : ZMod 97) ≠ 0 at hp
    change (8 : ZMod 97)-1 ≠ 0 at ha
    change (8 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((8 : ZMod 97)+1)) at hr
    change IsSquare (3-(8 : ZMod 97)) at hs
    change 97=7 → (8 : ZMod 97) ≠ 3 at h7
    change 97=11 → (8 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (92 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (9 : ZMod 97)
    change (9 : ZMod 97) ≠ 0 at hp
    change (9 : ZMod 97)-1 ≠ 0 at ha
    change (9 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((9 : ZMod 97)+1)) at hr
    change IsSquare (3-(9 : ZMod 97)) at hs
    change 97=7 → (9 : ZMod 97) ≠ 3 at h7
    change 97=11 → (9 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (10 : ZMod 97)
    change (10 : ZMod 97) ≠ 0 at hp
    change (10 : ZMod 97)-1 ≠ 0 at ha
    change (10 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((10 : ZMod 97)+1)) at hr
    change IsSquare (3-(10 : ZMod 97)) at hs
    change 97=7 → (10 : ZMod 97) ≠ 3 at h7
    change 97=11 → (10 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (90 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (11 : ZMod 97)
    change (11 : ZMod 97) ≠ 0 at hp
    change (11 : ZMod 97)-1 ≠ 0 at ha
    change (11 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((11 : ZMod 97)+1)) at hr
    change IsSquare (3-(11 : ZMod 97)) at hs
    change 97=7 → (11 : ZMod 97) ≠ 3 at h7
    change 97=11 → (11 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![37,0,40,33],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (12 : ZMod 97)
    change (12 : ZMod 97) ≠ 0 at hp
    change (12 : ZMod 97)-1 ≠ 0 at ha
    change (12 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((12 : ZMod 97)+1)) at hr
    change IsSquare (3-(12 : ZMod 97)) at hs
    change 97=7 → (12 : ZMod 97) ≠ 3 at h7
    change 97=11 → (12 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (13 : ZMod 97)
    change (13 : ZMod 97) ≠ 0 at hp
    change (13 : ZMod 97)-1 ≠ 0 at ha
    change (13 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((13 : ZMod 97)+1)) at hr
    change IsSquare (3-(13 : ZMod 97)) at hs
    change 97=7 → (13 : ZMod 97) ≠ 3 at h7
    change 97=11 → (13 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (14 : ZMod 97)
    change (14 : ZMod 97) ≠ 0 at hp
    change (14 : ZMod 97)-1 ≠ 0 at ha
    change (14 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((14 : ZMod 97)+1)) at hr
    change IsSquare (3-(14 : ZMod 97)) at hs
    change 97=7 → (14 : ZMod 97) ≠ 3 at h7
    change 97=11 → (14 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (30 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (15 : ZMod 97)
    change (15 : ZMod 97) ≠ 0 at hp
    change (15 : ZMod 97)-1 ≠ 0 at ha
    change (15 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((15 : ZMod 97)+1)) at hr
    change IsSquare (3-(15 : ZMod 97)) at hs
    change 97=7 → (15 : ZMod 97) ≠ 3 at h7
    change 97=11 → (15 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![15,2,30,41],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (16 : ZMod 97)
    change (16 : ZMod 97) ≠ 0 at hp
    change (16 : ZMod 97)-1 ≠ 0 at ha
    change (16 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((16 : ZMod 97)+1)) at hr
    change IsSquare (3-(16 : ZMod 97)) at hs
    change 97=7 → (16 : ZMod 97) ≠ 3 at h7
    change 97=11 → (16 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (34 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (17 : ZMod 97)
    change (17 : ZMod 97) ≠ 0 at hp
    change (17 : ZMod 97)-1 ≠ 0 at ha
    change (17 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((17 : ZMod 97)+1)) at hr
    change IsSquare (3-(17 : ZMod 97)) at hs
    change 97=7 → (17 : ZMod 97) ≠ 3 at h7
    change 97=11 → (17 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (83 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (18 : ZMod 97)
    change (18 : ZMod 97) ≠ 0 at hp
    change (18 : ZMod 97)-1 ≠ 0 at ha
    change (18 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((18 : ZMod 97)+1)) at hr
    change IsSquare (3-(18 : ZMod 97)) at hs
    change 97=7 → (18 : ZMod 97) ≠ 3 at h7
    change 97=11 → (18 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (38 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (19 : ZMod 97)
    change (19 : ZMod 97) ≠ 0 at hp
    change (19 : ZMod 97)-1 ≠ 0 at ha
    change (19 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((19 : ZMod 97)+1)) at hr
    change IsSquare (3-(19 : ZMod 97)) at hs
    change 97=7 → (19 : ZMod 97) ≠ 3 at h7
    change 97=11 → (19 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (40 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (20 : ZMod 97)
    change (20 : ZMod 97) ≠ 0 at hp
    change (20 : ZMod 97)-1 ≠ 0 at ha
    change (20 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((20 : ZMod 97)+1)) at hr
    change IsSquare (3-(20 : ZMod 97)) at hs
    change 97=7 → (20 : ZMod 97) ≠ 3 at h7
    change 97=11 → (20 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (42 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (21 : ZMod 97)
    change (21 : ZMod 97) ≠ 0 at hp
    change (21 : ZMod 97)-1 ≠ 0 at ha
    change (21 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((21 : ZMod 97)+1)) at hr
    change IsSquare (3-(21 : ZMod 97)) at hs
    change 97=7 → (21 : ZMod 97) ≠ 3 at h7
    change 97=11 → (21 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![11,47,5,15],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (22 : ZMod 97)
    change (22 : ZMod 97) ≠ 0 at hp
    change (22 : ZMod 97)-1 ≠ 0 at ha
    change (22 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((22 : ZMod 97)+1)) at hr
    change IsSquare (3-(22 : ZMod 97)) at hs
    change 97=7 → (22 : ZMod 97) ≠ 3 at h7
    change 97=11 → (22 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (46 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (23 : ZMod 97)
    change (23 : ZMod 97) ≠ 0 at hp
    change (23 : ZMod 97)-1 ≠ 0 at ha
    change (23 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((23 : ZMod 97)+1)) at hr
    change IsSquare (3-(23 : ZMod 97)) at hs
    change 97=7 → (23 : ZMod 97) ≠ 3 at h7
    change 97=11 → (23 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (77 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (24 : ZMod 97)
    change (24 : ZMod 97) ≠ 0 at hp
    change (24 : ZMod 97)-1 ≠ 0 at ha
    change (24 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((24 : ZMod 97)+1)) at hr
    change IsSquare (3-(24 : ZMod 97)) at hs
    change 97=7 → (24 : ZMod 97) ≠ 3 at h7
    change 97=11 → (24 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (76 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (25 : ZMod 97)
    change (25 : ZMod 97) ≠ 0 at hp
    change (25 : ZMod 97)-1 ≠ 0 at ha
    change (25 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((25 : ZMod 97)+1)) at hr
    change IsSquare (3-(25 : ZMod 97)) at hs
    change 97=7 → (25 : ZMod 97) ≠ 3 at h7
    change 97=11 → (25 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (52 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (26 : ZMod 97)
    change (26 : ZMod 97) ≠ 0 at hp
    change (26 : ZMod 97)-1 ≠ 0 at ha
    change (26 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((26 : ZMod 97)+1)) at hr
    change IsSquare (3-(26 : ZMod 97)) at hs
    change 97=7 → (26 : ZMod 97) ≠ 3 at h7
    change 97=11 → (26 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (74 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (27 : ZMod 97)
    change (27 : ZMod 97) ≠ 0 at hp
    change (27 : ZMod 97)-1 ≠ 0 at ha
    change (27 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((27 : ZMod 97)+1)) at hr
    change IsSquare (3-(27 : ZMod 97)) at hs
    change 97=7 → (27 : ZMod 97) ≠ 3 at h7
    change 97=11 → (27 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (56 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (28 : ZMod 97)
    change (28 : ZMod 97) ≠ 0 at hp
    change (28 : ZMod 97)-1 ≠ 0 at ha
    change (28 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((28 : ZMod 97)+1)) at hr
    change IsSquare (3-(28 : ZMod 97)) at hs
    change 97=7 → (28 : ZMod 97) ≠ 3 at h7
    change 97=11 → (28 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (58 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (29 : ZMod 97)
    change (29 : ZMod 97) ≠ 0 at hp
    change (29 : ZMod 97)-1 ≠ 0 at ha
    change (29 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((29 : ZMod 97)+1)) at hr
    change IsSquare (3-(29 : ZMod 97)) at hs
    change 97=7 → (29 : ZMod 97) ≠ 3 at h7
    change 97=11 → (29 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (60 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (30 : ZMod 97)
    change (30 : ZMod 97) ≠ 0 at hp
    change (30 : ZMod 97)-1 ≠ 0 at ha
    change (30 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((30 : ZMod 97)+1)) at hr
    change IsSquare (3-(30 : ZMod 97)) at hs
    change 97=7 → (30 : ZMod 97) ≠ 3 at h7
    change 97=11 → (30 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨42,![22,27,12,45],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (31 : ZMod 97)
    change (31 : ZMod 97) ≠ 0 at hp
    change (31 : ZMod 97)-1 ≠ 0 at ha
    change (31 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((31 : ZMod 97)+1)) at hr
    change IsSquare (3-(31 : ZMod 97)) at hs
    change 97=7 → (31 : ZMod 97) ≠ 3 at h7
    change 97=11 → (31 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (69 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (32 : ZMod 97)
    change (32 : ZMod 97) ≠ 0 at hp
    change (32 : ZMod 97)-1 ≠ 0 at ha
    change (32 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((32 : ZMod 97)+1)) at hr
    change IsSquare (3-(32 : ZMod 97)) at hs
    change 97=7 → (32 : ZMod 97) ≠ 3 at h7
    change 97=11 → (32 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (68 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (33 : ZMod 97)
    change (33 : ZMod 97) ≠ 0 at hp
    change (33 : ZMod 97)-1 ≠ 0 at ha
    change (33 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((33 : ZMod 97)+1)) at hr
    change IsSquare (3-(33 : ZMod 97)) at hs
    change 97=7 → (33 : ZMod 97) ≠ 3 at h7
    change 97=11 → (33 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (68 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (34 : ZMod 97)
    change (34 : ZMod 97) ≠ 0 at hp
    change (34 : ZMod 97)-1 ≠ 0 at ha
    change (34 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((34 : ZMod 97)+1)) at hr
    change IsSquare (3-(34 : ZMod 97)) at hs
    change 97=7 → (34 : ZMod 97) ≠ 3 at h7
    change 97=11 → (34 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,15,19,36],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (35 : ZMod 97)
    change (35 : ZMod 97) ≠ 0 at hp
    change (35 : ZMod 97)-1 ≠ 0 at ha
    change (35 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((35 : ZMod 97)+1)) at hr
    change IsSquare (3-(35 : ZMod 97)) at hs
    change 97=7 → (35 : ZMod 97) ≠ 3 at h7
    change 97=11 → (35 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![36,0,12,19],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (36 : ZMod 97)
    change (36 : ZMod 97) ≠ 0 at hp
    change (36 : ZMod 97)-1 ≠ 0 at ha
    change (36 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((36 : ZMod 97)+1)) at hr
    change IsSquare (3-(36 : ZMod 97)) at hs
    change 97=7 → (36 : ZMod 97) ≠ 3 at h7
    change 97=11 → (36 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (74 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (37 : ZMod 97)
    change (37 : ZMod 97) ≠ 0 at hp
    change (37 : ZMod 97)-1 ≠ 0 at ha
    change (37 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((37 : ZMod 97)+1)) at hr
    change IsSquare (3-(37 : ZMod 97)) at hs
    change 97=7 → (37 : ZMod 97) ≠ 3 at h7
    change 97=11 → (37 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (76 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (38 : ZMod 97)
    change (38 : ZMod 97) ≠ 0 at hp
    change (38 : ZMod 97)-1 ≠ 0 at ha
    change (38 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((38 : ZMod 97)+1)) at hr
    change IsSquare (3-(38 : ZMod 97)) at hs
    change 97=7 → (38 : ZMod 97) ≠ 3 at h7
    change 97=11 → (38 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (78 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (39 : ZMod 97)
    change (39 : ZMod 97) ≠ 0 at hp
    change (39 : ZMod 97)-1 ≠ 0 at ha
    change (39 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((39 : ZMod 97)+1)) at hr
    change IsSquare (3-(39 : ZMod 97)) at hs
    change 97=7 → (39 : ZMod 97) ≠ 3 at h7
    change 97=11 → (39 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (80 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (40 : ZMod 97)
    change (40 : ZMod 97) ≠ 0 at hp
    change (40 : ZMod 97)-1 ≠ 0 at ha
    change (40 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((40 : ZMod 97)+1)) at hr
    change IsSquare (3-(40 : ZMod 97)) at hs
    change 97=7 → (40 : ZMod 97) ≠ 3 at h7
    change 97=11 → (40 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (82 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (41 : ZMod 97)
    change (41 : ZMod 97) ≠ 0 at hp
    change (41 : ZMod 97)-1 ≠ 0 at ha
    change (41 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((41 : ZMod 97)+1)) at hr
    change IsSquare (3-(41 : ZMod 97)) at hs
    change 97=7 → (41 : ZMod 97) ≠ 3 at h7
    change 97=11 → (41 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (84 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (42 : ZMod 97)
    change (42 : ZMod 97) ≠ 0 at hp
    change (42 : ZMod 97)-1 ≠ 0 at ha
    change (42 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((42 : ZMod 97)+1)) at hr
    change IsSquare (3-(42 : ZMod 97)) at hs
    change 97=7 → (42 : ZMod 97) ≠ 3 at h7
    change 97=11 → (42 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (58 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (43 : ZMod 97)
    change (43 : ZMod 97) ≠ 0 at hp
    change (43 : ZMod 97)-1 ≠ 0 at ha
    change (43 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((43 : ZMod 97)+1)) at hr
    change IsSquare (3-(43 : ZMod 97)) at hs
    change 97=7 → (43 : ZMod 97) ≠ 3 at h7
    change 97=11 → (43 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (57 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (44 : ZMod 97)
    change (44 : ZMod 97) ≠ 0 at hp
    change (44 : ZMod 97)-1 ≠ 0 at ha
    change (44 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((44 : ZMod 97)+1)) at hr
    change IsSquare (3-(44 : ZMod 97)) at hs
    change 97=7 → (44 : ZMod 97) ≠ 3 at h7
    change 97=11 → (44 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (90 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (45 : ZMod 97)
    change (45 : ZMod 97) ≠ 0 at hp
    change (45 : ZMod 97)-1 ≠ 0 at ha
    change (45 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((45 : ZMod 97)+1)) at hr
    change IsSquare (3-(45 : ZMod 97)) at hs
    change 97=7 → (45 : ZMod 97) ≠ 3 at h7
    change 97=11 → (45 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (92 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (46 : ZMod 97)
    change (46 : ZMod 97) ≠ 0 at hp
    change (46 : ZMod 97)-1 ≠ 0 at ha
    change (46 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((46 : ZMod 97)+1)) at hr
    change IsSquare (3-(46 : ZMod 97)) at hs
    change 97=7 → (46 : ZMod 97) ≠ 3 at h7
    change 97=11 → (46 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![37,22,7,25],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (47 : ZMod 97)
    change (47 : ZMod 97) ≠ 0 at hp
    change (47 : ZMod 97)-1 ≠ 0 at ha
    change (47 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((47 : ZMod 97)+1)) at hr
    change IsSquare (3-(47 : ZMod 97)) at hs
    change 97=7 → (47 : ZMod 97) ≠ 3 at h7
    change 97=11 → (47 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![12,0,17,26],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (48 : ZMod 97)
    change (48 : ZMod 97) ≠ 0 at hp
    change (48 : ZMod 97)-1 ≠ 0 at ha
    change (48 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((48 : ZMod 97)+1)) at hr
    change IsSquare (3-(48 : ZMod 97)) at hs
    change 97=7 → (48 : ZMod 97) ≠ 3 at h7
    change 97=11 → (48 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (52 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (49 : ZMod 97)
    change (49 : ZMod 97) ≠ 0 at hp
    change (49 : ZMod 97)-1 ≠ 0 at ha
    change (49 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((49 : ZMod 97)+1)) at hr
    change IsSquare (3-(49 : ZMod 97)) at hs
    change 97=7 → (49 : ZMod 97) ≠ 3 at h7
    change 97=11 → (49 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (51 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (50 : ZMod 97)
    change (50 : ZMod 97) ≠ 0 at hp
    change (50 : ZMod 97)-1 ≠ 0 at ha
    change (50 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((50 : ZMod 97)+1)) at hr
    change IsSquare (3-(50 : ZMod 97)) at hs
    change 97=7 → (50 : ZMod 97) ≠ 3 at h7
    change 97=11 → (50 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (51 : ZMod 97)
    change (51 : ZMod 97) ≠ 0 at hp
    change (51 : ZMod 97)-1 ≠ 0 at ha
    change (51 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((51 : ZMod 97)+1)) at hr
    change IsSquare (3-(51 : ZMod 97)) at hs
    change 97=7 → (51 : ZMod 97) ≠ 3 at h7
    change 97=11 → (51 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (52 : ZMod 97)
    change (52 : ZMod 97) ≠ 0 at hp
    change (52 : ZMod 97)-1 ≠ 0 at ha
    change (52 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((52 : ZMod 97)+1)) at hr
    change IsSquare (3-(52 : ZMod 97)) at hs
    change 97=7 → (52 : ZMod 97) ≠ 3 at h7
    change 97=11 → (52 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨30,![28,40,45,15],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (53 : ZMod 97)
    change (53 : ZMod 97) ≠ 0 at hp
    change (53 : ZMod 97)-1 ≠ 0 at ha
    change (53 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((53 : ZMod 97)+1)) at hr
    change IsSquare (3-(53 : ZMod 97)) at hs
    change 97=7 → (53 : ZMod 97) ≠ 3 at h7
    change 97=11 → (53 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![21,0,33,3],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (54 : ZMod 97)
    change (54 : ZMod 97) ≠ 0 at hp
    change (54 : ZMod 97)-1 ≠ 0 at ha
    change (54 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((54 : ZMod 97)+1)) at hr
    change IsSquare (3-(54 : ZMod 97)) at hs
    change 97=7 → (54 : ZMod 97) ≠ 3 at h7
    change 97=11 → (54 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (55 : ZMod 97)
    change (55 : ZMod 97) ≠ 0 at hp
    change (55 : ZMod 97)-1 ≠ 0 at ha
    change (55 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((55 : ZMod 97)+1)) at hr
    change IsSquare (3-(55 : ZMod 97)) at hs
    change 97=7 → (55 : ZMod 97) ≠ 3 at h7
    change 97=11 → (55 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (56 : ZMod 97)
    change (56 : ZMod 97) ≠ 0 at hp
    change (56 : ZMod 97)-1 ≠ 0 at ha
    change (56 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((56 : ZMod 97)+1)) at hr
    change IsSquare (3-(56 : ZMod 97)) at hs
    change 97=7 → (56 : ZMod 97) ≠ 3 at h7
    change 97=11 → (56 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (17 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (57 : ZMod 97)
    change (57 : ZMod 97) ≠ 0 at hp
    change (57 : ZMod 97)-1 ≠ 0 at ha
    change (57 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((57 : ZMod 97)+1)) at hr
    change IsSquare (3-(57 : ZMod 97)) at hs
    change 97=7 → (57 : ZMod 97) ≠ 3 at h7
    change 97=11 → (57 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (19 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (58 : ZMod 97)
    change (58 : ZMod 97) ≠ 0 at hp
    change (58 : ZMod 97)-1 ≠ 0 at ha
    change (58 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((58 : ZMod 97)+1)) at hr
    change IsSquare (3-(58 : ZMod 97)) at hs
    change 97=7 → (58 : ZMod 97) ≠ 3 at h7
    change 97=11 → (58 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (21 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (59 : ZMod 97)
    change (59 : ZMod 97) ≠ 0 at hp
    change (59 : ZMod 97)-1 ≠ 0 at ha
    change (59 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((59 : ZMod 97)+1)) at hr
    change IsSquare (3-(59 : ZMod 97)) at hs
    change 97=7 → (59 : ZMod 97) ≠ 3 at h7
    change 97=11 → (59 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (23 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (60 : ZMod 97)
    change (60 : ZMod 97) ≠ 0 at hp
    change (60 : ZMod 97)-1 ≠ 0 at ha
    change (60 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((60 : ZMod 97)+1)) at hr
    change IsSquare (3-(60 : ZMod 97)) at hs
    change 97=7 → (60 : ZMod 97) ≠ 3 at h7
    change 97=11 → (60 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (40 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (61 : ZMod 97)
    change (61 : ZMod 97) ≠ 0 at hp
    change (61 : ZMod 97)-1 ≠ 0 at ha
    change (61 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((61 : ZMod 97)+1)) at hr
    change IsSquare (3-(61 : ZMod 97)) at hs
    change 97=7 → (61 : ZMod 97) ≠ 3 at h7
    change 97=11 → (61 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (62 : ZMod 97)
    change (62 : ZMod 97) ≠ 0 at hp
    change (62 : ZMod 97)-1 ≠ 0 at ha
    change (62 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((62 : ZMod 97)+1)) at hr
    change IsSquare (3-(62 : ZMod 97)) at hs
    change 97=7 → (62 : ZMod 97) ≠ 3 at h7
    change 97=11 → (62 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (63 : ZMod 97)
    change (63 : ZMod 97) ≠ 0 at hp
    change (63 : ZMod 97)-1 ≠ 0 at ha
    change (63 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((63 : ZMod 97)+1)) at hr
    change IsSquare (3-(63 : ZMod 97)) at hs
    change 97=7 → (63 : ZMod 97) ≠ 3 at h7
    change 97=11 → (63 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (37 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (64 : ZMod 97)
    change (64 : ZMod 97) ≠ 0 at hp
    change (64 : ZMod 97)-1 ≠ 0 at ha
    change (64 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((64 : ZMod 97)+1)) at hr
    change IsSquare (3-(64 : ZMod 97)) at hs
    change 97=7 → (64 : ZMod 97) ≠ 3 at h7
    change 97=11 → (64 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![8,0,39,15],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (65 : ZMod 97)
    change (65 : ZMod 97) ≠ 0 at hp
    change (65 : ZMod 97)-1 ≠ 0 at ha
    change (65 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((65 : ZMod 97)+1)) at hr
    change IsSquare (3-(65 : ZMod 97)) at hs
    change 97=7 → (65 : ZMod 97) ≠ 3 at h7
    change 97=11 → (65 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,39,36,39],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (66 : ZMod 97)
    change (66 : ZMod 97) ≠ 0 at hp
    change (66 : ZMod 97)-1 ≠ 0 at ha
    change (66 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((66 : ZMod 97)+1)) at hr
    change IsSquare (3-(66 : ZMod 97)) at hs
    change 97=7 → (66 : ZMod 97) ≠ 3 at h7
    change 97=11 → (66 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (37 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (67 : ZMod 97)
    change (67 : ZMod 97) ≠ 0 at hp
    change (67 : ZMod 97)-1 ≠ 0 at ha
    change (67 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((67 : ZMod 97)+1)) at hr
    change IsSquare (3-(67 : ZMod 97)) at hs
    change 97=7 → (67 : ZMod 97) ≠ 3 at h7
    change 97=11 → (67 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (39 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (68 : ZMod 97)
    change (68 : ZMod 97) ≠ 0 at hp
    change (68 : ZMod 97)-1 ≠ 0 at ha
    change (68 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((68 : ZMod 97)+1)) at hr
    change IsSquare (3-(68 : ZMod 97)) at hs
    change 97=7 → (68 : ZMod 97) ≠ 3 at h7
    change 97=11 → (68 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (41 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (69 : ZMod 97)
    change (69 : ZMod 97) ≠ 0 at hp
    change (69 : ZMod 97)-1 ≠ 0 at ha
    change (69 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((69 : ZMod 97)+1)) at hr
    change IsSquare (3-(69 : ZMod 97)) at hs
    change 97=7 → (69 : ZMod 97) ≠ 3 at h7
    change 97=11 → (69 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨21,![24,2,48,25],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (70 : ZMod 97)
    change (70 : ZMod 97) ≠ 0 at hp
    change (70 : ZMod 97)-1 ≠ 0 at ha
    change (70 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((70 : ZMod 97)+1)) at hr
    change IsSquare (3-(70 : ZMod 97)) at hs
    change 97=7 → (70 : ZMod 97) ≠ 3 at h7
    change 97=11 → (70 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (45 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (71 : ZMod 97)
    change (71 : ZMod 97) ≠ 0 at hp
    change (71 : ZMod 97)-1 ≠ 0 at ha
    change (71 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((71 : ZMod 97)+1)) at hr
    change IsSquare (3-(71 : ZMod 97)) at hs
    change 97=7 → (71 : ZMod 97) ≠ 3 at h7
    change 97=11 → (71 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (29 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (72 : ZMod 97)
    change (72 : ZMod 97) ≠ 0 at hp
    change (72 : ZMod 97)-1 ≠ 0 at ha
    change (72 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((72 : ZMod 97)+1)) at hr
    change IsSquare (3-(72 : ZMod 97)) at hs
    change 97=7 → (72 : ZMod 97) ≠ 3 at h7
    change 97=11 → (72 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (28 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (73 : ZMod 97)
    change (73 : ZMod 97) ≠ 0 at hp
    change (73 : ZMod 97)-1 ≠ 0 at ha
    change (73 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((73 : ZMod 97)+1)) at hr
    change IsSquare (3-(73 : ZMod 97)) at hs
    change 97=7 → (73 : ZMod 97) ≠ 3 at h7
    change 97=11 → (73 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (51 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (74 : ZMod 97)
    change (74 : ZMod 97) ≠ 0 at hp
    change (74 : ZMod 97)-1 ≠ 0 at ha
    change (74 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((74 : ZMod 97)+1)) at hr
    change IsSquare (3-(74 : ZMod 97)) at hs
    change 97=7 → (74 : ZMod 97) ≠ 3 at h7
    change 97=11 → (74 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (26 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (75 : ZMod 97)
    change (75 : ZMod 97) ≠ 0 at hp
    change (75 : ZMod 97)-1 ≠ 0 at ha
    change (75 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((75 : ZMod 97)+1)) at hr
    change IsSquare (3-(75 : ZMod 97)) at hs
    change 97=7 → (75 : ZMod 97) ≠ 3 at h7
    change 97=11 → (75 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (55 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (76 : ZMod 97)
    change (76 : ZMod 97) ≠ 0 at hp
    change (76 : ZMod 97)-1 ≠ 0 at ha
    change (76 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((76 : ZMod 97)+1)) at hr
    change IsSquare (3-(76 : ZMod 97)) at hs
    change 97=7 → (76 : ZMod 97) ≠ 3 at h7
    change 97=11 → (76 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (57 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (77 : ZMod 97)
    change (77 : ZMod 97) ≠ 0 at hp
    change (77 : ZMod 97)-1 ≠ 0 at ha
    change (77 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((77 : ZMod 97)+1)) at hr
    change IsSquare (3-(77 : ZMod 97)) at hs
    change 97=7 → (77 : ZMod 97) ≠ 3 at h7
    change 97=11 → (77 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (59 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (78 : ZMod 97)
    change (78 : ZMod 97) ≠ 0 at hp
    change (78 : ZMod 97)-1 ≠ 0 at ha
    change (78 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((78 : ZMod 97)+1)) at hr
    change IsSquare (3-(78 : ZMod 97)) at hs
    change 97=7 → (78 : ZMod 97) ≠ 3 at h7
    change 97=11 → (78 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨15,![43,33,43,19],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (79 : ZMod 97)
    change (79 : ZMod 97) ≠ 0 at hp
    change (79 : ZMod 97)-1 ≠ 0 at ha
    change (79 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((79 : ZMod 97)+1)) at hr
    change IsSquare (3-(79 : ZMod 97)) at hs
    change 97=7 → (79 : ZMod 97) ≠ 3 at h7
    change 97=11 → (79 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (63 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (80 : ZMod 97)
    change (80 : ZMod 97) ≠ 0 at hp
    change (80 : ZMod 97)-1 ≠ 0 at ha
    change (80 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((80 : ZMod 97)+1)) at hr
    change IsSquare (3-(80 : ZMod 97)) at hs
    change 97=7 → (80 : ZMod 97) ≠ 3 at h7
    change 97=11 → (80 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (20 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (81 : ZMod 97)
    change (81 : ZMod 97) ≠ 0 at hp
    change (81 : ZMod 97)-1 ≠ 0 at ha
    change (81 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((81 : ZMod 97)+1)) at hr
    change IsSquare (3-(81 : ZMod 97)) at hs
    change 97=7 → (81 : ZMod 97) ≠ 3 at h7
    change 97=11 → (81 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (67 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (82 : ZMod 97)
    change (82 : ZMod 97) ≠ 0 at hp
    change (82 : ZMod 97)-1 ≠ 0 at ha
    change (82 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((82 : ZMod 97)+1)) at hr
    change IsSquare (3-(82 : ZMod 97)) at hs
    change 97=7 → (82 : ZMod 97) ≠ 3 at h7
    change 97=11 → (82 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (69 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (83 : ZMod 97)
    change (83 : ZMod 97) ≠ 0 at hp
    change (83 : ZMod 97)-1 ≠ 0 at ha
    change (83 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((83 : ZMod 97)+1)) at hr
    change IsSquare (3-(83 : ZMod 97)) at hs
    change 97=7 → (83 : ZMod 97) ≠ 3 at h7
    change 97=11 → (83 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (71 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (84 : ZMod 97)
    change (84 : ZMod 97) ≠ 0 at hp
    change (84 : ZMod 97)-1 ≠ 0 at ha
    change (84 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((84 : ZMod 97)+1)) at hr
    change IsSquare (3-(84 : ZMod 97)) at hs
    change 97=7 → (84 : ZMod 97) ≠ 3 at h7
    change 97=11 → (84 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨30,![17,35,41,21],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (85 : ZMod 97)
    change (85 : ZMod 97) ≠ 0 at hp
    change (85 : ZMod 97)-1 ≠ 0 at ha
    change (85 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((85 : ZMod 97)+1)) at hr
    change IsSquare (3-(85 : ZMod 97)) at hs
    change 97=7 → (85 : ZMod 97) ≠ 3 at h7
    change 97=11 → (85 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (15 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (86 : ZMod 97)
    change (86 : ZMod 97) ≠ 0 at hp
    change (86 : ZMod 97)-1 ≠ 0 at ha
    change (86 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((86 : ZMod 97)+1)) at hr
    change IsSquare (3-(86 : ZMod 97)) at hs
    change 97=7 → (86 : ZMod 97) ≠ 3 at h7
    change 97=11 → (86 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (77 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (87 : ZMod 97)
    change (87 : ZMod 97) ≠ 0 at hp
    change (87 : ZMod 97)-1 ≠ 0 at ha
    change (87 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((87 : ZMod 97)+1)) at hr
    change IsSquare (3-(87 : ZMod 97)) at hs
    change 97=7 → (87 : ZMod 97) ≠ 3 at h7
    change 97=11 → (87 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (13 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (88 : ZMod 97)
    change (88 : ZMod 97) ≠ 0 at hp
    change (88 : ZMod 97)-1 ≠ 0 at ha
    change (88 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((88 : ZMod 97)+1)) at hr
    change IsSquare (3-(88 : ZMod 97)) at hs
    change 97=7 → (88 : ZMod 97) ≠ 3 at h7
    change 97=11 → (88 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨1,![31,0,29,46],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (89 : ZMod 97)
    change (89 : ZMod 97) ≠ 0 at hp
    change (89 : ZMod 97)-1 ≠ 0 at ha
    change (89 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((89 : ZMod 97)+1)) at hr
    change IsSquare (3-(89 : ZMod 97)) at hs
    change 97=7 → (89 : ZMod 97) ≠ 3 at h7
    change 97=11 → (89 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (83 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (90 : ZMod 97)
    change (90 : ZMod 97) ≠ 0 at hp
    change (90 : ZMod 97)-1 ≠ 0 at ha
    change (90 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((90 : ZMod 97)+1)) at hr
    change IsSquare (3-(90 : ZMod 97)) at hs
    change 97=7 → (90 : ZMod 97) ≠ 3 at h7
    change 97=11 → (90 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (10 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (91 : ZMod 97)
    change (91 : ZMod 97) ≠ 0 at hp
    change (91 : ZMod 97)-1 ≠ 0 at ha
    change (91 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((91 : ZMod 97)+1)) at hr
    change IsSquare (3-(91 : ZMod 97)) at hs
    change 97=7 → (91 : ZMod 97) ≠ 3 at h7
    change 97=11 → (91 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (87 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hr using 1 <;> decide
  · change Charts (92 : ZMod 97)
    change (92 : ZMod 97) ≠ 0 at hp
    change (92 : ZMod 97)-1 ≠ 0 at ha
    change (92 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((92 : ZMod 97)+1)) at hr
    change IsSquare (3-(92 : ZMod 97)) at hs
    change 97=7 → (92 : ZMod 97) ≠ 3 at h7
    change 97=11 → (92 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,20,34,44],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (93 : ZMod 97)
    change (93 : ZMod 97) ≠ 0 at hp
    change (93 : ZMod 97)-1 ≠ 0 at ha
    change (93 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((93 : ZMod 97)+1)) at hr
    change IsSquare (3-(93 : ZMod 97)) at hs
    change 97=7 → (93 : ZMod 97) ≠ 3 at h7
    change 97=11 → (93 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (7 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (94 : ZMod 97)
    change (94 : ZMod 97) ≠ 0 at hp
    change (94 : ZMod 97)-1 ≠ 0 at ha
    change (94 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((94 : ZMod 97)+1)) at hr
    change IsSquare (3-(94 : ZMod 97)) at hs
    change 97=7 → (94 : ZMod 97) ≠ 3 at h7
    change 97=11 → (94 : ZMod 97) ≠ 5 at h11
    apply Or.inl
    refine ⟨0,![0,28,44,17],?_⟩
    intro i
    fin_cases i <;> decide
  · change Charts (95 : ZMod 97)
    change (95 : ZMod 97) ≠ 0 at hp
    change (95 : ZMod 97)-1 ≠ 0 at ha
    change (95 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((95 : ZMod 97)+1)) at hr
    change IsSquare (3-(95 : ZMod 97)) at hs
    change 97=7 → (95 : ZMod 97) ≠ 3 at h7
    change 97=11 → (95 : ZMod 97) ≠ 5 at h11
    have hn : ¬IsSquare (5 : ZMod 97) := by decide
    apply False.elim
    apply hn
    convert hs using 1 <;> decide
  · change Charts (96 : ZMod 97)
    change (96 : ZMod 97) ≠ 0 at hp
    change (96 : ZMod 97)-1 ≠ 0 at ha
    change (96 : ZMod 97)+1 ≠ 0 at hb
    change IsSquare (2*((96 : ZMod 97)+1)) at hr
    change IsSquare (3-(96 : ZMod 97)) at hs
    change 97=7 → (96 : ZMod 97) ≠ 3 at h7
    change 97=11 → (96 : ZMod 97) ≠ 5 at h11
    exact False.elim (hb (by decide))


#print axioms charts97

end
end FourCorner.HpSmallResidue
