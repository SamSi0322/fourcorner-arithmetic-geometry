import PaperCommonSourceCriterion

noncomputable section
namespace FourCorner.CommonSource
open OrderedSplit

/-- The literal local square test, prior to any source packaging. -/
def AllowedOddProbe.squareAt {n : ℤ} {hn : n ≠ 0} (d : AllowedOddProbe n hn) (a c : ℚ) : Prop := by
  letI : Fact d.q.Prime := ⟨d.prime⟩
  exact IsSquare (commonSourceReturn (n:ℚ_[d.q]) a c)

/-- Exclusion stated directly on the original rational coordinates and the
original two ordered Kummer slots. All source square witnesses and all H
remainders are constructed by the verified paper-source adapter. -/
theorem literal_paper_source_exclusion {n : ℤ} (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) {s : ℕ} (probes : Fin s → AllowedOddProbe n hn)
    (hn8 : n%8=1 ∨ n%8=7) (hcompl : IsCompl (H n hn) (twoTorsion (n:ℚ)))
    (W : H n hn) (hW : ActualPair.DistinguishedRow W)
    (hW0 : parity (LogPrecision.paperLogCharacter n hn k hk hdeep W)=0)
    (hbeta : beta (paperSourceRows n hn k hk hdeep probes)
      (kernelClass (paperSourceRows n hn k hk hdeep probes) W
        (paperSourceRows_W_even hn k hk hdeep probes hn8 hcompl W hW hW0)) ≠ 0)
    {a b c e : ℚ} (han : -(n:ℚ)<a) (ha : a<0) (hc : (n:ℚ)<c)
    (hQ : CongruentEquation (n:ℚ) a b) (hR : CongruentEquation (n:ℚ) c e)
    (h0 : kummerDelta (n:ℚ) (by exact_mod_cast hn)
        (Multiplicative.ofAdd (finitePoint (by exact_mod_cast hn) hQ)) 0 *
      kummerDelta (n:ℚ) (by exact_mod_cast hn)
        (Multiplicative.ofAdd (finitePoint (by exact_mod_cast hn) hR)) 0=
      scalarClass (-(n:ℚ)) (by exact_mod_cast (neg_ne_zero.mpr hn)))
    (h1 : kummerDelta (n:ℚ) (by exact_mod_cast hn)
        (Multiplicative.ofAdd (finitePoint (by exact_mod_cast hn) hQ)) 1 *
      kummerDelta (n:ℚ) (by exact_mod_cast hn)
        (Multiplicative.ofAdd (finitePoint (by exact_mod_cast hn) hR)) 1=
      scalarClass (-(n:ℚ)) (by exact_mod_cast (neg_ne_zero.mpr hn)))
    (hf : Even (commonSourceReturn (n:ℚ_[2]) a c).valuation)
    (hloc : ∀ j, (probes j).squareAt a c) : False := by
  have hnpos : 0 < (n:ℚ) := by linarith
  obtain ⟨S,hSa,hSb,hSc,hSe⟩ := exists_actual_pair_from_paper hn hnpos hcompl han ha hc hQ hR h0 h1 hf
  apply common_source_character_criterion hn k hk hdeep probes hn8 hcompl W hW hW0 hbeta
  refine ⟨S,fun j => ?_⟩
  change (probes j).squareAt S.a S.c
  rw [hSa,hSc]
  exact hloc j

#print axioms literal_paper_source_exclusion
#print axioms common_source_character_criterion
#print axioms common_source_character_certificate
#print axioms LogPrecision.paper_primitive_source_module_pullback
#print axioms LogPrecision.wholeLogInteger_paper_value
end FourCorner.CommonSource
