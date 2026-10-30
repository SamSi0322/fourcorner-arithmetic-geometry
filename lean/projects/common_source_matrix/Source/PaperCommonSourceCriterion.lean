import CoordinateRingPullback
import ActualDyadicSourceSign
import OddRowFull

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource
open scoped BigOperators

/-- A genuine permitted odd-prime probe, with its actual whole-H image and
literal local squareness data. Its character is constructed, not supplied. -/
structure AllowedOddProbe (n : ℤ) (hn : n ≠ 0) where
  q : ℕ
  prime : q.Prime
  residue_five : q%8=5
  good : (n:ZMod q) ≠ 0
  square_n : letI : Fact q.Prime := ⟨prime⟩; IsSquare (n:ℚ_[q])
  actual : letI : Fact q.Prime := ⟨prime⟩; ActualOddProbe n hn q (by omega) good

namespace AllowedOddProbe
variable {n : ℤ} {hn : n ≠ 0}
def character (d : AllowedOddProbe n hn) : H n hn →+ ZMod 4 := by
  letI : Fact d.q.Prime := ⟨d.prime⟩
  exact d.actual.character

def squareReturn (d : AllowedOddProbe n hn) (S : ActualPair n hn) : Prop := by
  letI : Fact d.q.Prime := ⟨d.prime⟩
  exact IsSquare (commonSourceReturn (n:ℚ_[d.q]) S.a S.c)

theorem row (d : AllowedOddProbe n hn) (hn8 : n%8=1 ∨ n%8=7)
    (hcompl : IsCompl (H n hn) (twoTorsion (n:ℚ)))
    (W : H n hn) (hW : ActualPair.DistinguishedRow W) :
    parity (d.character W)=0 ∧ ∀ S : ActualPair n hn, d.squareReturn S →
      d.character S.U=d.character S.V ∧ (d.character S.U=0 ∨ d.character S.U=2) := by
  letI : Fact d.q.Prime := ⟨d.prime⟩
  exact common_source_odd_row hn8 hcompl W hW d.residue_five d.good d.square_n d.actual
end AllowedOddProbe

/-- The actual paper log character, followed by all fixed permitted odd probes. -/
def paperSourceRows (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) {s : ℕ}
    (probes : Fin s → AllowedOddProbe n hn) : Fin (s+1) → H n hn →+ F4 :=
  Fin.cases (LogPrecision.paperLogCharacter n hn k hk hdeep) (fun j => (probes j).character)

theorem paperSourceRows_W_even {n : ℤ} (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) {s : ℕ} (probes : Fin s → AllowedOddProbe n hn)
    (hn8 : n%8=1 ∨ n%8=7) (hcompl : IsCompl (H n hn) (twoTorsion (n:ℚ)))
    (W : H n hn) (hW : ActualPair.DistinguishedRow W)
    (hW0 : parity (LogPrecision.paperLogCharacter n hn k hk hdeep W)=0) :
    eta (paperSourceRows n hn k hk hdeep probes) W=0 := by
  ext j
  change parity (paperSourceRows n hn k hk hdeep probes j W)=0
  refine Fin.cases ?_ (fun j => ?_) j
  · exact hW0
  · exact ((probes j).row hn8 hcompl W hW).1

theorem actual_source_paper_log_sign {n : ℤ} (hn : n ≠ 0)
    (hn8 : n%8=1 ∨ n%8=7) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) (S : ActualPair n hn) :
    LogPrecision.paperLogCharacter n hn k hk hdeep S.V=
      LogPrecision.paperLogCharacter n hn k hk hdeep S.U ∨
    LogPrecision.paperLogCharacter n hn k hk hdeep S.V=
      -LogPrecision.paperLogCharacter n hn k hk hdeep S.U := by
  rw [LogPrecision.paperLogCharacter_eq_parameter]
  have h := actual_source_dyadic_sign hn hn8 k hk hdeep S.hQ S.hR
    S.a_ne S.c_ne S.am_ne S.cm_ne S.ap_ne S.cp_ne S.hu S.hv S.U S.V
    S.tauQ S.tauR S.htQ S.htR S.hQU S.hRV S.hf
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    simpa only [neg_neg] using (congrArg Neg.neg h).symm

/-- One actual source satisfying all specified local tests forces the secondary
invariant of the SAME global class to vanish. The full H/2H is retained. -/
theorem paper_beta_zero_of_source {n : ℤ} (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) {s : ℕ} (probes : Fin s → AllowedOddProbe n hn)
    (hn8 : n%8=1 ∨ n%8=7) (hcompl : IsCompl (H n hn) (twoTorsion (n:ℚ)))
    (W : H n hn) (hW : ActualPair.DistinguishedRow W)
    (hW0 : parity (LogPrecision.paperLogCharacter n hn k hk hdeep W)=0)
    (S : ActualPair n hn) (hlocal : ∀ j, (probes j).squareReturn S) :
    let phi := paperSourceRows n hn k hk hdeep probes
    let he := paperSourceRows_W_even hn k hk hdeep probes hn8 hcompl W hW hW0
    beta phi (kernelClass phi W he)=0 := by
  let phi := paperSourceRows n hn k hk hdeep probes
  have he := paperSourceRows_W_even hn k hk hdeep probes hn8 hcompl W hW hW0
  obtain ⟨Z,hsource⟩ := S.complete_coset hn8 hcompl W hW
  apply beta_eq_zero_of_pair phi (0:Fin (s+1)) (kernelClass phi W he) rfl hsource
  · exact actual_source_paper_log_sign hn hn8 k hk hdeep S
  · intro j
    refine Fin.cases (fun h => False.elim (h rfl)) (fun j _ => ?_) j
    exact ((probes j).row hn8 hcompl W hW).2 S (hlocal j)

/-- The exclusion conclusion of paper thm:cs-matrix, with actual original
source objects, actual permitted probes and the normalized dx/(2y) log. -/
theorem common_source_character_criterion {n : ℤ} (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) {s : ℕ} (probes : Fin s → AllowedOddProbe n hn)
    (hn8 : n%8=1 ∨ n%8=7) (hcompl : IsCompl (H n hn) (twoTorsion (n:ℚ)))
    (W : H n hn) (hW : ActualPair.DistinguishedRow W)
    (hW0 : parity (LogPrecision.paperLogCharacter n hn k hk hdeep W)=0) :
    let phi := paperSourceRows n hn k hk hdeep probes
    let he := paperSourceRows_W_even hn k hk hdeep probes hn8 hcompl W hW hW0
    beta phi (kernelClass phi W he) ≠ 0 →
      ¬ ∃ S : ActualPair n hn, ∀ j, (probes j).squareReturn S := by
  intro phi he hbeta hsource
  obtain ⟨S,hlocal⟩ := hsource
  exact hbeta (paper_beta_zero_of_source hn k hk hdeep probes hn8 hcompl W hW hW0 S hlocal)

/-- The exact finite half-weighted certificate equivalence in the same paper
theorem; it is equivalence to beta nonvanishing, not to all possible no-point facts. -/
theorem common_source_character_certificate {n : ℤ} (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) {s : ℕ} (probes : Fin s → AllowedOddProbe n hn)
    (hn8 : n%8=1 ∨ n%8=7) (hcompl : IsCompl (H n hn) (twoTorsion (n:ℚ)))
    (W : H n hn) (hW : ActualPair.DistinguishedRow W)
    (hW0 : parity (LogPrecision.paperLogCharacter n hn k hk hdeep W)=0) :
    let phi := paperSourceRows n hn k hk hdeep probes
    let he := paperSourceRows_W_even hn k hk hdeep probes hn8 hcompl W hW hW0
    beta phi (kernelClass phi W he) ≠ 0 ↔
      ∃ c : Fin (s+1) → F2, (∀ Z : H n hn, ∑ j, c j*eta phi Z j=0) ∧
        half (weightedCharacter phi c W)=1 := by
  intro phi he
  exact beta_ne_zero_iff_weighted_certificate phi (kernelClass phi W he) rfl

#print axioms AllowedOddProbe.character
#print axioms paperSourceRows_W_even
#print axioms paper_beta_zero_of_source
#print axioms common_source_character_criterion
#print axioms common_source_character_certificate
#print axioms LogPrecision.original_coordinate_differential_pullback
#print axioms LogPrecision.wholeLogInteger_paper_value
end FourCorner.CommonSource
