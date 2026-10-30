import ThetaLinesAbsoluteGalois
import ThetaLinesContactPoints
import ThetaBitangentCountWave36

namespace FourCorner.ThetaLinesProjectiveClassification
open ThetaLinesProjectiveLines ThetaLinesAbsoluteGalois
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

def displayedList {k : Type*} [Field k] (r s : k) : List (ThetaLine k) := [
.affine (r/2) 0,
.affine 0 (r/2),
.affine (-r/2) 0,
.affine 0 (-r/2),
.affine (5*r) 0,
.affine 0 (5*r),
.affine (-5*r) 0,
.affine 0 (-5*r),
.affine (9/14) (9/14),
.affine (9/14) (-9/14),
.affine (-9/14) (9/14),
.affine (-9/14) (-9/14),
.affine (11/14) (11/14),
.affine (11/14) (-11/14),
.affine (-11/14) (11/14),
.affine (-11/14) (-11/14),
.affine (s*(9)/102) (s*(11)/102),
.affine (s*(9)/102) (s*(-11)/102),
.affine (s*(-9)/102) (s*(11)/102),
.affine (s*(-9)/102) (s*(-11)/102),
.affine (s*(11)/102) (s*(9)/102),
.affine (s*(11)/102) (s*(-9)/102),
.affine (s*(-11)/102) (s*(9)/102),
.affine (s*(-11)/102) (s*(-9)/102),
.vertical ((1)*r*(s+7*(1))/2),
.vertical ((1)*r*(s+7*(-1))/2),
.vertical ((-1)*r*(s+7*(1))/2),
.vertical ((-1)*r*(s+7*(-1))/2)]

theorem square_contact_iff_list {k : Type*} [Field k] [CharZero k] (r s : k) (hr : r^2=2) (hs : s^2=51) (L : ThetaLine k) :
    IsThetaSquareContact L ↔ L ∈ displayedList r s := by
  constructor
  · intro h
    have hh := (theta_square_contact_displayed_iff r s
      hr hs L).mp h
    rcases hh with ⟨u,hu,hL | hL⟩ | ⟨ε,η,he,hh,hL | hL⟩ | ⟨ε,η,he,hh,hL | hL⟩ | ⟨ε,η,he,hh,hL⟩
    all_goals subst L
    · obtain ⟨ε,he,hu | hu⟩ := (theta_axis_radical_parameters r u hr).mp hu
      all_goals rcases sq_eq_one_iff.mp he with rfl | rfl
      all_goals rw [hu]; norm_num [displayedList]
    · obtain ⟨ε,he,hu | hu⟩ := (theta_axis_radical_parameters r u hr).mp hu
      all_goals rcases sq_eq_one_iff.mp he with rfl | rfl
      all_goals rw [hu]; norm_num [displayedList]
    all_goals rcases sq_eq_one_iff.mp he with rfl | rfl
    all_goals rcases sq_eq_one_iff.mp hh with rfl | rfl
    all_goals norm_num [displayedList, mul_neg, neg_mul, mul_assoc]
  · intro h
    apply (theta_no_hyperflex L).mpr
    simp only [displayedList,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · rw [h]; apply theta_bitangent_I_half; norm_num [div_pow,mul_pow,hr]
    · rw [h]; apply theta_bitangent_I_half_swap; norm_num [div_pow,mul_pow,hr]
    · rw [h]; apply theta_bitangent_I_half; norm_num [div_pow,mul_pow,hr]
    · rw [h]; apply theta_bitangent_I_half_swap; norm_num [div_pow,mul_pow,hr]
    · rw [h]; apply theta_bitangent_I_fifty; norm_num [div_pow,mul_pow,hr]
    · rw [h]; apply theta_bitangent_I_fifty_swap; norm_num [div_pow,mul_pow,hr]
    · rw [h]; apply theta_bitangent_I_fifty; norm_num [div_pow,mul_pow,hr]
    · rw [h]; apply theta_bitangent_I_fifty_swap; norm_num [div_pow,mul_pow,hr]
    · rw [h]; convert theta_bitangent_II_nine (1:k) (1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_nine (1:k) (-1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_nine (-1:k) (1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_nine (-1:k) (-1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_eleven (1:k) (1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_eleven (1:k) (-1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_eleven (-1:k) (1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_II_eleven (-1:k) (-1) (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_nine_eleven s (1) (1) hs (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_nine_eleven s (1) (-1) hs (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_nine_eleven s (-1) (1) hs (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_nine_eleven s (-1) (-1) hs (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_eleven_nine s (1) (1) hs (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_eleven_nine s (1) (-1) hs (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_eleven_nine s (-1) (1) hs (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; convert theta_bitangent_III_eleven_nine s (-1) (-1) hs (by norm_num) (by norm_num) using 1 <;> norm_num
    · rw [h]; exact theta_bitangent_IV r s (1) (1) hr hs (by norm_num) (by norm_num)
    · rw [h]; exact theta_bitangent_IV r s (1) (-1) hr hs (by norm_num) (by norm_num)
    · rw [h]; exact theta_bitangent_IV r s (-1) (1) hr hs (by norm_num) (by norm_num)
    · rw [h]; exact theta_bitangent_IV r s (-1) (-1) hr hs (by norm_num) (by norm_num)


def mapLine {A B : Type*} [Field A] [Field B] (f : A →+* B) : ThetaLine A → ThetaLine B
  | .affine a b => .affine (f a) (f b)
  | .vertical t => .vertical (f t)
  | .yzero => .yzero

theorem mapLine_injective {A B : Type*} [Field A] [Field B] (f : A →+* B) : Function.Injective (mapLine f) := by
  intro L M h
  cases L <;> cases M <;> simp_all [mapLine,f.injective.eq_iff]

theorem displayedList_embedding : displayedList r s=thetaTwentyEightLines.map (mapLine splittingEmbedding.toRingHom) := by
  simp [displayedList,thetaTwentyEightLines,mapLine,r,s,map_ofNat]

theorem displayedList_nodup : (displayedList r s).Nodup := by
  rw [displayedList_embedding]
  exact theta_twenty_eight_distinct.map (mapLine_injective splittingEmbedding.toRingHom)

/-- The displayed list as actual native points of the projective plane of
homogeneous linear forms, rather than an abstract set of 28 labels. -/
def actualDisplayedLines : List (Projectivization Qbar (Fin 3 → Qbar)) :=
  (displayedList r s).map geometricLine

theorem actualDisplayedLines_nodup : actualDisplayedLines.Nodup :=
  displayedList_nodup.map geometricLine_injective

theorem actualDisplayedLines_length : actualDisplayedLines.length=28 := by
  rfl

/-- This condition is the literal quartic square-restriction condition in
proved normalized charts of the ACTUAL projective line. It is independent
of the displayed list. The Cartier/Pic odd-theta bridge is a separate goal. -/
def nativeSquareContact (P : Projectivization Qbar (Fin 3 → Qbar)) : Prop :=
  IsThetaSquareContact (lineEquiv.symm P)

theorem native_square_contact_classification (P : Projectivization Qbar (Fin 3 → Qbar)) :
    nativeSquareContact P ↔ P∈actualDisplayedLines := by
  constructor
  · intro h
    have hm := (square_contact_iff_list r s r_sq s_sq (lineEquiv.symm P)).mp h
    exact List.mem_map.mpr ⟨lineEquiv.symm P,hm,lineEquiv.apply_symm_apply P⟩
  · intro h
    obtain ⟨L,hL,he⟩ := List.mem_map.mp h
    subst P
    apply (square_contact_iff_list r s r_sq s_sq _).mpr
    change lineEquiv.symm (lineEquiv L) ∈ displayedList r s
    simpa only [Equiv.symm_apply_apply] using hL

#print axioms square_contact_iff_list
#print axioms displayedList_nodup
#print axioms actualDisplayedLines_nodup
#print axioms actualDisplayedLines_length
#print axioms native_square_contact_classification
end
end FourCorner.ThetaLinesProjectiveClassification
