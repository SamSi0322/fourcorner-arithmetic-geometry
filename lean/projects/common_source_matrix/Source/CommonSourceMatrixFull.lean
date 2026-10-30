import PaperCommonSourceRaw

noncomputable section
namespace FourCorner.CommonSource
open scoped BigOperators

/-- Complete paper thm:cs-matrix: the original logarithmic source criterion
and its exact half-weighted certificate equivalence, for the entire actual H. -/
theorem common_source_matrix {n : ℤ} (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) {s : ℕ} (probes : Fin s → AllowedOddProbe n hn)
    (hn8 : n%8=1 ∨ n%8=7) (hcompl : IsCompl (H n hn) (twoTorsion (n:ℚ)))
    (W : H n hn) (hW : ActualPair.DistinguishedRow W)
    (hW0 : parity (LogPrecision.paperLogCharacter n hn k hk hdeep W)=0) :
    let phi := paperSourceRows n hn k hk hdeep probes
    let he := paperSourceRows_W_even hn k hk hdeep probes hn8 hcompl W hW hW0
    let kap := kernelClass phi W he
    (beta phi kap ≠ 0 → ¬ ∃ S : ActualPair n hn, ∀ j, (probes j).squareReturn S) ∧
    (beta phi kap ≠ 0 ↔ ∃ c : Fin (s+1) → F2,
      (∀ Z : H n hn, ∑ j, c j*eta phi Z j=0) ∧ half (weightedCharacter phi c W)=1) := by
  exact ⟨common_source_character_criterion hn k hk hdeep probes hn8 hcompl W hW hW0,
    common_source_character_certificate hn k hk hdeep probes hn8 hcompl W hW hW0⟩

#print axioms common_source_matrix
#print axioms literal_paper_source_exclusion
#print axioms LogPrecision.paper_primitive_source_module_pullback
#print axioms LogPrecision.coordinateEvaluation_denominator
#print axioms LogPrecision.paperEllSeries_eq_canonical
#print axioms LogPrecision.paperLog_hasSum
#print axioms LogPrecision.wholeLogInteger_paper_value
end FourCorner.CommonSource
