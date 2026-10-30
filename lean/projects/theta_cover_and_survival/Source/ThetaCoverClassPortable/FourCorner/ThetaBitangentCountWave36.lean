import ThetaCoverClassPortable.FourCorner.ThetaBitangentExhaustionWave36
import ThetaCoverClassPortable.FourCorner.ThetaBitangentGaloisWave36
set_option maxHeartbeats 2000000
namespace FourCorner
open scoped QuadraticAlgebra
/-- All actual normalized lines from the displayed list, over the genuine splitting field. -/
def thetaTwentyEightLines : List (ThetaLine ThetaBiquadratic) := [
.affine (thetaGaloisR/2) 0,
.affine 0 (thetaGaloisR/2),
.affine (-thetaGaloisR/2) 0,
.affine 0 (-thetaGaloisR/2),
.affine (5*thetaGaloisR) 0,
.affine 0 (5*thetaGaloisR),
.affine (-5*thetaGaloisR) 0,
.affine 0 (-5*thetaGaloisR),
.affine (9/14) (9/14),
.affine (9/14) (-9/14),
.affine (-9/14) (9/14),
.affine (-9/14) (-9/14),
.affine (11/14) (11/14),
.affine (11/14) (-11/14),
.affine (-11/14) (11/14),
.affine (-11/14) (-11/14),
.affine (thetaGaloisS*(9)/102) (thetaGaloisS*(11)/102),
.affine (thetaGaloisS*(9)/102) (thetaGaloisS*(-11)/102),
.affine (thetaGaloisS*(-9)/102) (thetaGaloisS*(11)/102),
.affine (thetaGaloisS*(-9)/102) (thetaGaloisS*(-11)/102),
.affine (thetaGaloisS*(11)/102) (thetaGaloisS*(9)/102),
.affine (thetaGaloisS*(11)/102) (thetaGaloisS*(-9)/102),
.affine (thetaGaloisS*(-11)/102) (thetaGaloisS*(9)/102),
.affine (thetaGaloisS*(-11)/102) (thetaGaloisS*(-9)/102),
.vertical ((1)*thetaGaloisR*(thetaGaloisS+7*(1))/2),
.vertical ((1)*thetaGaloisR*(thetaGaloisS+7*(-1))/2),
.vertical ((-1)*thetaGaloisR*(thetaGaloisS+7*(1))/2),
.vertical ((-1)*thetaGaloisR*(thetaGaloisS+7*(-1))/2)]

@[simp] theorem theta_affine_ne_vertical {K : Type*} (a b t : K) :
    ThetaLine.affine a b ≠ ThetaLine.vertical t := by intro h; cases h

/-- The displayed list consists of twenty-eight distinct actual normalized lines. -/
theorem theta_twenty_eight_distinct : thetaTwentyEightLines.Nodup := by
  norm_num [thetaTwentyEightLines, List.nodup_cons, QuadraticAlgebra.ext_iff,
    thetaGaloisR, thetaGaloisS, QuadraticAlgebra.omega,
    div_eq_mul_inv, QuadraticAlgebra.inv_def, QuadraticAlgebra.norm_def]

theorem theta_twenty_eight_length : thetaTwentyEightLines.length = 28 := by rfl
#print axioms theta_twenty_eight_distinct

/-- Exhaustive list classification, rather than a collection of witnesses. -/
theorem theta_all_square_contacts_list (L : ThetaLine ThetaBiquadratic) :
    IsThetaSquareContact L ↔ L ∈ thetaTwentyEightLines := by
  constructor
  · intro h
    have hh := (theta_square_contact_displayed_iff thetaGaloisR thetaGaloisS
      thetaGaloisR_sq thetaGaloisS_sq L).mp h
    rcases hh with ⟨u,hu,hL | hL⟩ | ⟨ε,η,he,hh,hL | hL⟩ | ⟨ε,η,he,hh,hL | hL⟩ | ⟨ε,η,he,hh,hL⟩
    all_goals subst L
    · obtain ⟨ε,he,hu | hu⟩ := (theta_axis_radical_parameters thetaGaloisR u thetaGaloisR_sq).mp hu
      all_goals rcases sq_eq_one_iff.mp he with rfl | rfl
      all_goals rw [hu]; norm_num [thetaTwentyEightLines]
    · obtain ⟨ε,he,hu | hu⟩ := (theta_axis_radical_parameters thetaGaloisR u thetaGaloisR_sq).mp hu
      all_goals rcases sq_eq_one_iff.mp he with rfl | rfl
      all_goals rw [hu]; norm_num [thetaTwentyEightLines]
    all_goals rcases sq_eq_one_iff.mp he with rfl | rfl
    all_goals rcases sq_eq_one_iff.mp hh with rfl | rfl
    all_goals norm_num [thetaTwentyEightLines, mul_neg, neg_mul, mul_assoc]
  · intro h
    apply (theta_no_hyperflex L).mpr
    simp only [thetaTwentyEightLines,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [h]; apply theta_bitangent_I_half; norm_num [div_pow,mul_pow,thetaGaloisR_sq]
    · rw [h]; apply theta_bitangent_I_half_swap; norm_num [div_pow,mul_pow,thetaGaloisR_sq]
    · rw [h]; apply theta_bitangent_I_half; norm_num [div_pow,mul_pow,thetaGaloisR_sq]
    · rw [h]; apply theta_bitangent_I_half_swap; norm_num [div_pow,mul_pow,thetaGaloisR_sq]
    · rw [h]; apply theta_bitangent_I_fifty; norm_num [div_pow,mul_pow,thetaGaloisR_sq]
    · rw [h]; apply theta_bitangent_I_fifty_swap; norm_num [div_pow,mul_pow,thetaGaloisR_sq]
    · rw [h]; apply theta_bitangent_I_fifty; norm_num [div_pow,mul_pow,thetaGaloisR_sq]
    · rw [h]; apply theta_bitangent_I_fifty_swap; norm_num [div_pow,mul_pow,thetaGaloisR_sq]
    · rw [h]; convert theta_bitangent_II_nine (1:ThetaBiquadratic) (1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_nine (1:ThetaBiquadratic) (-1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_nine (-1:ThetaBiquadratic) (1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_nine (-1:ThetaBiquadratic) (-1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_eleven (1:ThetaBiquadratic) (1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_eleven (1:ThetaBiquadratic) (-1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_eleven (-1:ThetaBiquadratic) (1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_eleven (-1:ThetaBiquadratic) (-1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_nine_eleven thetaGaloisS (1) (1) thetaGaloisS_sq (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_nine_eleven thetaGaloisS (1) (-1) thetaGaloisS_sq (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_nine_eleven thetaGaloisS (-1) (1) thetaGaloisS_sq (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_nine_eleven thetaGaloisS (-1) (-1) thetaGaloisS_sq (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_eleven_nine thetaGaloisS (1) (1) thetaGaloisS_sq (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_eleven_nine thetaGaloisS (1) (-1) thetaGaloisS_sq (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_eleven_nine thetaGaloisS (-1) (1) thetaGaloisS_sq (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_eleven_nine thetaGaloisS (-1) (-1) thetaGaloisS_sq (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; exact theta_bitangent_IV thetaGaloisR thetaGaloisS (1) (1) thetaGaloisR_sq thetaGaloisS_sq (by norm_num) (by norm_num)
    · rw [h]; exact theta_bitangent_IV thetaGaloisR thetaGaloisS (1) (-1) thetaGaloisR_sq thetaGaloisS_sq (by norm_num) (by norm_num)
    · rw [h]; exact theta_bitangent_IV thetaGaloisR thetaGaloisS (-1) (1) thetaGaloisR_sq thetaGaloisS_sq (by norm_num) (by norm_num)
    · rw [h]; exact theta_bitangent_IV thetaGaloisR thetaGaloisS (-1) (-1) thetaGaloisR_sq thetaGaloisS_sq (by norm_num) (by norm_num)

#print axioms theta_all_square_contacts_list
end FourCorner
