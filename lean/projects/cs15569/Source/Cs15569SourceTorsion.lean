import Cs15569DyadicGeneration
import ActualBranch15569

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section

/-- The exact actual torsion translations, rather than only their abscissae,
for the same strict source pair. All rejected orders are proved impossible. -/
theorem actual_source_torsion_labels (S : ActualPair 15569 n15569_ne_zero) (r : S.Remainders) :
    S.tauQ=Tminus 15569 (by norm_num) ∧ S.tauR=Tplus 15569 (by norm_num) := by
  have hs := source_kummer_sum (by norm_num) S.hQ S.hR S.a_ne S.c_ne S.am_ne S.cm_ne
    S.ap_ne S.cp_ne S.hu S.hv
  have ht := source_torsion_sum_one 15569 n15569_ne_zero (by decide)
    (finitePoint (by norm_num) S.hQ) (finitePoint (by norm_num) S.hR)
    S.U S.V S.tauQ S.tauR S.U.property S.V.property S.hQU S.hRV S.htQ S.htR hs
  have hQU : finitePoint (by norm_num) S.hQ=finitePoint (by norm_num) r.hU+S.tauQ := by
    rw [←r.eqU]
    exact S.hQU
  have hRV : finitePoint (by norm_num) S.hR=finitePoint (by norm_num) r.hV+S.tauR := by
    rw [←r.eqV]
    exact S.hRV
  have hxdata := actual_H_coordinate_data n15569_ne_zero r.hU r.memU
  have hwdata := actual_H_coordinate_data n15569_ne_zero r.hV r.memV
  have hxv := (some_mem_H_iff 15569 n15569_ne_zero r.x r.y (nonsingular (by norm_num) r.hU)).mp r.memU
  have hreal := depth_two_real_identity r.hU hxv
  rcases torsion_pairs_one 15569 (by norm_num) S.tauQ S.tauR S.htQ ht with h0 | hO | hgood | hplus
  · have ha : S.a=commonSourceTranslateZero (15569 : ℚ) r.x := by
      rw [h0.1] at hQU
      exact abscissa_add_T0 (by norm_num) S.hQ r.hU hxdata.1 hQU
    have hc : S.c=r.w := by
      rw [h0.2] at hRV
      exact abscissa_add_zero (by norm_num) S.hR r.hV hRV
    have ha' : (S.a : ℚ_[2])=commonSourceTranslateZero (15569 : ℚ_[2]) r.x := by
      dsimp [commonSourceTranslateZero] at ha ⊢
      exact_mod_cast ha
    have hc' : (S.c : ℚ_[2])=(r.w : ℚ_[2]) := by exact_mod_cast hc
    have hn2 := commonSource_dyadic_odd_int_unit (show Odd (15569 : ℤ) by decide)
    have hf : Even (commonSourceReturn (15569 : ℚ_[2]) S.a S.c).valuation := by
      simpa only [Int.cast_ofNat] using S.hf
    rw [ha',hc',commonSource_dyadic_return_zero_identity_val (n:=(15569 : ℚ_[2]))
      (by norm_num) (by simpa only [Int.cast_ofNat] using hn2.2) hxdata.2.2.2.1 hwdata.2.2.2.1] at hf
    obtain ⟨j,hj⟩ := hf
    omega
  · have ha : S.a=r.x := by
      rw [hO.1] at hQU
      exact abscissa_add_zero (by norm_num) S.hQ r.hU hQU
    linarith [S.ha]
  · exact hgood
  · have ha : S.a=commonSourceTranslatePlus (15569 : ℚ) r.x := by
      rw [hplus.1] at hQU
      exact abscissa_add_Tplus (by norm_num) S.hQ r.hU hxdata.2.1 hQU
    have hpos : 0<S.a := by
      rw [ha]
      unfold commonSourceTranslatePlus
      have hd : 0<r.x-15569 := by linarith
      positivity
    linarith [S.ha]

#print axioms actual_source_torsion_labels
end
end FourCorner.Cs15569Completion
