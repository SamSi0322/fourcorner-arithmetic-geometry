import Cs15569ReturnExclusion113
import ActualPairPaperAdapter
import SourceLayer17

/-! Complete exact source exclusion thm:cs-15569 and its original strict
rational-distance layer corollary. No rank, splitting, generation, residue
image or bounded-height premise is included in either numbered statement. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace FourCorner.Cs15569Completion
open CommonSource OrderedSplit
noncomputable section

theorem n15569_ne_rat : (15569 : ℚ) ≠ 0 := by norm_num

/-- thm:cs-15569, on arbitrary finite rational Q=(a,b), R=(c,e), their
literal two ordered Kummer products, strict intervals, and the same literal
return square in Q2,Q3,Q113. All actual group/source infrastructure is proved. -/
theorem cs15569_source_exclusion {a b c e : ℚ}
    (han : -(15569 : ℚ)<a) (ha : a<0) (hc : 15569<c)
    (hQ : CongruentEquation 15569 a b) (hR : CongruentEquation 15569 c e)
    (h0 : δ (finitePoint n15569_ne_rat hQ) 0*δ (finitePoint n15569_ne_rat hR) 0=
      scalarClass (-15569 : ℚ) (by norm_num))
    (h1 : δ (finitePoint n15569_ne_rat hQ) 1*δ (finitePoint n15569_ne_rat hR) 1=
      scalarClass (-15569 : ℚ) (by norm_num))
    (hs2 : IsSquare (commonSourceReturn (15569 : ℚ_[2]) a c))
    (hs3 : IsSquare (commonSourceReturn (15569 : ℚ_[3]) a c))
    (hs113 : IsSquare (commonSourceReturn (15569 : ℚ_[113]) a c)) : False := by
  have hsum := two_paper_slots_full_sum n15569_ne_rat
    (finitePoint n15569_ne_rat hQ) (finitePoint n15569_ne_rat hR) h0 h1
  obtain ⟨u,v,hu,hv⟩ := (source_squares_iff_kummer_sum n15569_ne_rat hQ hR
    (by linarith : a ≠ 0) (by linarith : c ≠ 0)
    (by linarith : a-15569 ≠ 0) (by linarith : c-15569 ≠ 0)
    (by linarith : a+15569 ≠ 0) (by linarith : c+15569 ≠ 0)).mpr hsum
  obtain ⟨S,hSa,hSb,hSc,hSe⟩ := raw_source_actual_pair han ha hc hQ hR hu hv hs2
  apply actual_pair_exclusion S
  · simpa only [hSa,hSc] using hs2
  · simpa only [hSa,hSc] using hs3
  · simpa only [hSa,hSc] using hs113

/-- The identical numbered source statement with f retained explicitly as a
rational value before its canonical embedding into all three completed fields. -/
theorem cs15569_source_exclusion_cast {a b c e : ℚ}
    (han : -(15569 : ℚ)<a) (ha : a<0) (hc : 15569<c)
    (hQ : CongruentEquation 15569 a b) (hR : CongruentEquation 15569 c e)
    (h0 : δ (finitePoint n15569_ne_rat hQ) 0*δ (finitePoint n15569_ne_rat hR) 0=
      scalarClass (-15569 : ℚ) (by norm_num))
    (h1 : δ (finitePoint n15569_ne_rat hQ) 1*δ (finitePoint n15569_ne_rat hR) 1=
      scalarClass (-15569 : ℚ) (by norm_num))
    (hs2 : IsSquare (((a+c)/(2*(c+15569)) : ℚ) : ℚ_[2]))
    (hs3 : IsSquare (((a+c)/(2*(c+15569)) : ℚ) : ℚ_[3]))
    (hs113 : IsSquare (((a+c)/(2*(c+15569)) : ℚ) : ℚ_[113])) : False := by
  apply cs15569_source_exclusion han ha hc hQ hR h0 h1
  · simpa [commonSourceReturn] using hs2
  · simpa [commonSourceReturn] using hs3
  · simpa [commonSourceReturn] using hs113

/-- The original-source bridge is used only downstream of the completed raw
source theorem. It supplies the SAME ordered slots and literal final square. -/
theorem ordered_core_15569_impossible (s : OrderedCore (15569 : ℚ)) : False := by
  have hsum := source_kummer_sum n15569_ne_rat s.hQ s.hR s.a_ne s.c_ne s.am_ne s.cm_ne
    s.ap_ne s.cp_ne s.hu2 s.hv2
  have h0 := congrFun hsum 0
  have h1 := congrFun hsum 1
  rw [kummerDelta_add,Pi.mul_apply] at h0 h1
  have hs := SourceLayer17.three_local_squares s
  apply cs15569_source_exclusion s.han s.ha s.hc s.hQ s.hR h0 h1
  · simpa only [commonSourceReturn,Rat.cast_ofNat] using hs.1
  · simpa only [commonSourceReturn,Rat.cast_ofNat] using hs.2.1
  · simpa only [commonSourceReturn,Rat.cast_ofNat] using hs.2.2

/-- cor:cs-15569-layer for every original strict rational-distance
configuration, its original labelled radii, and the canonical sf(t²-1). -/
theorem cs15569_layer {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    rationalSquarefreePart ((r₀*r₃+r₁*r₂)^2-1) ≠ 15569 := by
  intro hkernel
  obtain ⟨s,hn,hf,hsq⟩ := SourceLayer17.original_source h
  have hn' : s.1.1=15569 := by
    rw [hn]
    exact hkernel
  have hnq : (s.1.1 : ℚ)=15569 := by exact_mod_cast hn'
  have s15569 : OrderedCore (15569 : ℚ) := hnq ▸ s.2.1
  exact ordered_core_15569_impossible s15569

#print axioms cs15569_source_exclusion
#print axioms cs15569_source_exclusion_cast
#print axioms ordered_core_15569_impossible
#print axioms cs15569_layer
end
end FourCorner.Cs15569Completion
