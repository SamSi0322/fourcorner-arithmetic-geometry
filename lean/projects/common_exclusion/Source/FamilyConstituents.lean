import Mathlib.Algebra.Field.ZMod
import FourCorner.CommonRootPadicResidue
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import FourCorner.CommonRootSource

namespace FourCorner

def commonFamilyDelta : ℕ := 1926281441

def commonFamilyC : ℕ := 269297

def commonFamilyK : ℕ := 2 ^ 20 * 7 * 37

/-- The prescribed rational perturbations of the initial common-root parameter. -/
def commonFamilyQ (j : ℕ) : ℚ :=
  1 / (commonFamilyC : ℚ) +
    (commonFamilyK : ℚ) / (1 + (commonFamilyK : ℚ) ^ 2 * j)

/-- The resulting rational parameter of the common-root family. -/
def commonFamilyT (j : ℕ) : ℚ :=
  (1 + (commonFamilyDelta : ℚ) * commonFamilyQ j ^ 2) /
    (1 - (commonFamilyDelta : ℚ) * commonFamilyQ j ^ 2)

/-- The square factor in `t_j² - 1`. -/
def commonFamilyScale (j : ℕ) : ℚ :=
  2 * commonFamilyQ j / (1 - (commonFamilyDelta : ℚ) * commonFamilyQ j ^ 2)

lemma commonFamilyDelta_pos : (0 : ℚ) < commonFamilyDelta := by
  norm_num [commonFamilyDelta]

lemma commonFamilyK_pos : (0 : ℚ) < commonFamilyK := by
  norm_num [commonFamilyK]

lemma commonFamily_den_pos (j : ℕ) :
    (0 : ℚ) < 1 + (commonFamilyK : ℚ) ^ 2 * j := by positivity

theorem commonFamilyQ_pos (j : ℕ) : 0 < commonFamilyQ j := by
  apply add_pos
  · norm_num [commonFamilyC]
  · exact div_pos commonFamilyK_pos (commonFamily_den_pos j)

/-- The perturbation, and hence its rational parameter, strictly decreases. -/
theorem commonFamilyQ_strictAnti : StrictAnti commonFamilyQ := by
  intro i j hij
  unfold commonFamilyQ
  apply (add_lt_add_iff_left _).mpr
  apply div_lt_div_of_pos_left commonFamilyK_pos (commonFamily_den_pos i)
  have hijq : (i : ℚ) < j := by exact_mod_cast hij
  have hk : (0 : ℚ) < (commonFamilyK : ℚ) ^ 2 := sq_pos_of_pos commonFamilyK_pos
  linarith [mul_lt_mul_of_pos_left hijq hk]

/-- An exact rational certificate bounds every positive-index perturbation. -/
theorem commonFamily_small (j : ℕ) (hj : 1 ≤ j) :
    (commonFamilyDelta : ℚ) * commonFamilyQ j ^ 2 < 1 / 33 := by
  have hqle : commonFamilyQ j ≤ commonFamilyQ 1 := commonFamilyQ_strictAnti.antitone hj
  have hsqle : commonFamilyQ j ^ 2 ≤ commonFamilyQ 1 ^ 2 :=
    (sq_le_sq₀ (commonFamilyQ_pos j).le (commonFamilyQ_pos 1).le).mpr hqle
  have hbound : (commonFamilyDelta : ℚ) * commonFamilyQ 1 ^ 2 < 1 / 33 := by
    norm_num [commonFamilyDelta, commonFamilyQ, commonFamilyC, commonFamilyK]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsqle commonFamilyDelta_pos.le) hbound

lemma commonFamily_mobius_den_pos (j : ℕ) (hj : 1 ≤ j) :
    (0 : ℚ) < 1 - (commonFamilyDelta : ℚ) * commonFamilyQ j ^ 2 := by
  have hsmall := commonFamily_small j hj
  linarith

theorem commonFamilyScale_pos (j : ℕ) (hj : 1 ≤ j) : 0 < commonFamilyScale j :=
  div_pos (mul_pos (by norm_num) (commonFamilyQ_pos j)) (commonFamily_mobius_den_pos j hj)

/-- Exact initial parameter appearing in the manuscript. -/
theorem commonFamily_initial_t :
    (1 + (commonFamilyDelta : ℚ) * (1 / (commonFamilyC : ℚ)) ^ 2) /
      (1 - (commonFamilyDelta : ℚ) * (1 / (commonFamilyC : ℚ)) ^ 2) =
      138225 / 131072 := by norm_num [commonFamilyDelta, commonFamilyC]

theorem commonFamily_initial_den :
    1 - (commonFamilyDelta : ℚ) * (1 / (commonFamilyC : ℚ)) ^ 2 =
      2 ^ 18 / (commonFamilyC : ℚ) := by norm_num [commonFamilyDelta, commonFamilyC]

end FourCorner

namespace FourCorner

theorem family_parameter_bounds (j : ℕ) (hj : 1 ≤ j) :
    1 < commonFamilyT j ∧ commonFamilyT j < 17 / 16 := by
  have hp : 0 < (commonFamilyDelta : ℚ) * commonFamilyQ j ^ 2 :=
    mul_pos commonFamilyDelta_pos (sq_pos_of_pos (commonFamilyQ_pos j))
  have hs := commonFamily_small j hj
  have hd := commonFamily_mobius_den_pos j hj
  unfold commonFamilyT
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    linarith

theorem family_parameter_strictAnti :
    StrictAnti (fun j : {n : ℕ // 1 ≤ n} => commonFamilyT j.val) := by
  intro i j hij
  have hq := commonFamilyQ_strictAnti hij
  have hsq : commonFamilyQ j.val ^ 2 < commonFamilyQ i.val ^ 2 := by
    nlinarith [commonFamilyQ_pos j.val, commonFamilyQ_pos i.val]
  have hm := mul_lt_mul_of_pos_left hsq commonFamilyDelta_pos
  have hi := commonFamily_mobius_den_pos i.val i.property
  have hj := commonFamily_mobius_den_pos j.val j.property
  unfold commonFamilyT
  apply (div_lt_div_iff₀ hj hi).mpr
  nlinarith

theorem family_parameter_injective :
    Function.Injective (fun j : {n : ℕ // 1 ≤ n} => commonFamilyT j.val) :=
  family_parameter_strictAnti.injective

theorem family_discriminant_identity (j : ℕ) (hj : 1 ≤ j) :
    commonFamilyT j ^ 2 - 1 = (commonFamilyDelta : ℚ) * commonFamilyScale j ^ 2 := by
  have hd := ne_of_gt (commonFamily_mobius_den_pos j hj)
  unfold commonFamilyT commonFamilyScale
  field_simp
  <;> ring

end FourCorner

#print axioms FourCorner.family_parameter_bounds
#print axioms FourCorner.family_parameter_injective
#print axioms FourCorner.family_discriminant_identity

namespace FourCorner

theorem family_upper_real : (17 / 16 : ℝ) < Real.sqrt 5 / 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  nlinarith

end FourCorner
#print axioms FourCorner.family_upper_real

namespace FourCorner
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem family_delta_not_square : ¬ IsSquare (commonFamilyDelta : ℚ) := by
  norm_num [commonFamilyDelta]

theorem family_delta_not_twice_square : ¬ IsSquare ((commonFamilyDelta : ℚ) / 2) := by
  norm_num [commonFamilyDelta]

theorem family_den_valuation (j : ℕ) :
    padicValRat 7 (1 + (commonFamilyK : ℚ)^2*j) = 0 := by
  have hn : ¬ 7 ∣ 1 + commonFamilyK^2*j := by
    simp [Nat.dvd_iff_mod_eq_zero, commonFamilyK, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  have heq : (1 + (commonFamilyK : ℚ)^2*j) = ((1 + commonFamilyK^2*j : ℕ) : ℚ) := by
    push_cast
    rfl
  rw [heq, padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd hn

lemma family_seven_nat_val_zero (n : ℕ) (hn : ¬ 7 ∣ n) : padicValRat 7 (n : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd hn

lemma family_seven_nat_val_one (n : ℕ) (hn : ¬ 7 ∣ n) (hn0 : n ≠ 0) :
    padicValRat 7 ((7*n : ℕ) : ℚ) = 1 := by
  rw [Nat.cast_mul, padicValRat.mul (by norm_num) (by exact_mod_cast hn0),
    family_seven_nat_val_zero n hn]
  change padicValRat 7 ((7 : ℕ) : ℚ) + 0 = 1
  rw [padicValRat.of_nat, padicValNat.self (by norm_num : 1 < 7)]
  norm_num

theorem family_q_valuation (j : ℕ) : padicValRat 7 (commonFamilyQ j) = -1 := by
  have hbase : padicValRat 7 (1 / (commonFamilyC : ℚ)) = -1 := by
    rw [one_div, padicValRat.inv]
    have h : (commonFamilyC : ℚ) = ((7*38471 : ℕ) : ℚ) := by norm_num [commonFamilyC]
    rw [h, family_seven_nat_val_one 38471 (by norm_num) (by norm_num)]
  have hk : padicValRat 7 (commonFamilyK : ℚ) = 1 := by
    have h : (commonFamilyK : ℚ) = ((7*38797312 : ℕ) : ℚ) := by norm_num [commonFamilyK]
    rw [h, family_seven_nat_val_one 38797312 (by norm_num) (by norm_num)]
  have hpert : padicValRat 7 ((commonFamilyK : ℚ) / (1 + (commonFamilyK : ℚ)^2*j)) = 1 := by
    rw [padicValRat.div (ne_of_gt commonFamilyK_pos) (ne_of_gt (commonFamily_den_pos j)),
      hk, family_den_valuation]
    norm_num
  unfold commonFamilyQ
  rw [padicValRat.add_eq_min]
  · rw [hbase, hpert]; norm_num
  · exact ne_of_gt (commonFamilyQ_pos j)
  · norm_num [commonFamilyC]
  · exact ne_of_gt (div_pos commonFamilyK_pos (commonFamily_den_pos j))
  · rw [hbase, hpert]; norm_num

end FourCorner
#print axioms FourCorner.family_delta_not_square
#print axioms FourCorner.family_delta_not_twice_square
#print axioms FourCorner.family_q_valuation

namespace FourCorner
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem family_mobius_den_valuation (j : ℕ) (hj : 1 ≤ j) :
    padicValRat 7 (1-(commonFamilyDelta : ℚ)*commonFamilyQ j ^ 2) = -1 := by
  have hdelta : padicValRat 7 (commonFamilyDelta : ℚ) = 1 := by
    have h : (commonFamilyDelta : ℚ) = ((7*275183063 : ℕ) : ℚ) := by norm_num [commonFamilyDelta]
    rw [h, family_seven_nat_val_one 275183063 (by norm_num) (by norm_num)]
  have hv : padicValRat 7 ((commonFamilyDelta : ℚ)*commonFamilyQ j ^ 2) = -1 := by
    rw [padicValRat.mul (ne_of_gt commonFamilyDelta_pos)
      (pow_ne_zero 2 (ne_of_gt (commonFamilyQ_pos j))), padicValRat.pow,
      hdelta, family_q_valuation]
    norm_num
  rw [sub_eq_add_neg]
  rw [padicValRat.add_eq_min]
  · rw [padicValRat.one, padicValRat.neg, hv]; norm_num
  · simpa only [sub_eq_add_neg] using ne_of_gt (commonFamily_mobius_den_pos j hj)
  · norm_num
  · exact neg_ne_zero.mpr (mul_ne_zero (ne_of_gt commonFamilyDelta_pos)
      (pow_ne_zero 2 (ne_of_gt (commonFamilyQ_pos j))))
  · rw [padicValRat.one, padicValRat.neg, hv]; norm_num

theorem family_t_add_one_identity (j : ℕ) (hj : 1 ≤ j) :
    commonFamilyT j + 1 = 2 / (1-(commonFamilyDelta : ℚ)*commonFamilyQ j ^ 2) := by
  have hd := ne_of_gt (commonFamily_mobius_den_pos j hj)
  unfold commonFamilyT
  field_simp
  <;> ring

theorem family_t_add_one_valuation (j : ℕ) (hj : 1 ≤ j) :
    padicValRat 7 (commonFamilyT j+1) = 1 := by
  rw [family_t_add_one_identity j hj,
    padicValRat.div (by norm_num) (ne_of_gt (commonFamily_mobius_den_pos j hj)),
    family_mobius_den_valuation j hj]
  have h2 : padicValRat 7 (2 : ℚ) = 0 := family_seven_nat_val_zero 2 (by norm_num)
  rw [h2]
  norm_num

theorem family_t_add_one_not_square (j : ℕ) (hj : 1 ≤ j) :
    ¬ IsSquare (commonFamilyT j+1) := by
  rintro ⟨r, hr⟩
  have hv := family_t_add_one_valuation j hj
  rw [hr, ← pow_two, padicValRat.pow] at hv
  omega

theorem family_t_add_one_not_twice_square (j : ℕ) (hj : 1 ≤ j) :
    ¬ ∃ r : ℚ, commonFamilyT j+1 = 2*r^2 := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    intro hz
    have hb := (family_parameter_bounds j hj).1
    rw [hz] at hr
    norm_num at hr
    linarith
  have hv := family_t_add_one_valuation j hj
  rw [hr, padicValRat.mul (by norm_num) (pow_ne_zero 2 hr0), padicValRat.pow] at hv
  have htwo : padicValRat 7 2 = 0 := by exact family_seven_nat_val_zero 2 (by norm_num)
  rw [htwo] at hv
  omega
end FourCorner
#print axioms FourCorner.family_t_add_one_not_square
#print axioms FourCorner.family_t_add_one_not_twice_square

namespace FourCorner

theorem family_discriminant_not_square (j : ℕ) (hj : 1 ≤ j) :
    ¬ IsSquare (commonFamilyT j ^ 2-1) := by
  intro hs
  have hv := hs.div (IsSquare.sq (commonFamilyScale j))
  rw [family_discriminant_identity j hj,
    mul_div_cancel_right₀ _ (pow_ne_zero 2 (ne_of_gt (commonFamilyScale_pos j hj)))] at hv
  exact family_delta_not_square hv

theorem family_discriminant_not_twice_square (j : ℕ) (hj : 1 ≤ j) :
    ¬ ∃ r : ℚ, commonFamilyT j ^ 2-1 = 2*r^2 := by
  rintro ⟨r, hr⟩
  apply family_delta_not_twice_square
  refine ⟨r / commonFamilyScale j, ?_⟩
  have hid := family_discriminant_identity j hj
  have hn := ne_of_gt (commonFamilyScale_pos j hj)
  rw [← pow_two, div_pow]
  symm
  apply (div_eq_iff (pow_ne_zero 2 hn)).mpr
  rw [hr] at hid
  linarith
end FourCorner
#print axioms FourCorner.family_discriminant_not_square
#print axioms FourCorner.family_discriminant_not_twice_square

namespace FourCorner

def familyA (j : ℕ) : ℤ := 1 + (commonFamilyK : ℤ)^2*j
def familyB (j : ℕ) : ℤ := familyA j + commonFamilyC*commonFamilyK
def familyN (j : ℕ) : ℤ := (commonFamilyC : ℤ)^2 * familyA j ^2 + commonFamilyDelta * familyB j ^2
def familyD (j : ℕ) : ℤ := (commonFamilyC : ℤ)^2 * familyA j ^2 - commonFamilyDelta * familyB j ^2

theorem family_cleared_parameter (j : ℕ) (hj : 1 ≤ j) :
    commonFamilyT j = (familyN j : ℚ) / (familyD j : ℚ) := by
  have ha := ne_of_gt (commonFamily_den_pos j)
  have hd := ne_of_gt (commonFamily_mobius_den_pos j hj)
  unfold commonFamilyT commonFamilyQ familyN familyD familyB familyA
  push_cast
  norm_num [commonFamilyC] at *
  field_simp
  <;> ring

theorem family_N_residue (j : ℕ) : (familyN j : ZMod 37) = 31 := by
  unfold familyN familyB familyA
  push_cast
  have hc : (commonFamilyC : ZMod 37) = 11 := by
    apply (ZMod.natCast_eq_natCast_iff' _ 11 37).mpr
    norm_num [commonFamilyC]
  have hk : (commonFamilyK : ZMod 37) = 0 := by
    apply (ZMod.natCast_eq_natCast_iff' _ 0 37).mpr
    norm_num [commonFamilyK]
  have hd : (commonFamilyDelta : ZMod 37) = 21 := by
    apply (ZMod.natCast_eq_natCast_iff' _ 21 37).mpr
    norm_num [commonFamilyDelta]
  rw [hc, hk, hd]
  norm_num
  decide

theorem family_D_residue (j : ℕ) : (familyD j : ZMod 37) = 26 := by
  unfold familyD familyB familyA
  push_cast
  have hc : (commonFamilyC : ZMod 37) = 11 := by
    apply (ZMod.natCast_eq_natCast_iff' _ 11 37).mpr
    norm_num [commonFamilyC]
  have hk : (commonFamilyK : ZMod 37) = 0 := by
    apply (ZMod.natCast_eq_natCast_iff' _ 0 37).mpr
    norm_num [commonFamilyK]
  have hd : (commonFamilyDelta : ZMod 37) = 21 := by
    apply (ZMod.natCast_eq_natCast_iff' _ 21 37).mpr
    norm_num [commonFamilyDelta]
  rw [hc, hk, hd]
  norm_num
  decide

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

theorem family_residue_quotient (j : ℕ) : (familyN j : ZMod 37) / (familyD j : ZMod 37) = 14 := by
  rw [family_N_residue, family_D_residue]
  apply (div_eq_iff (by decide : (26 : ZMod 37) ≠ 0)).mpr
  decide
end FourCorner
#print axioms FourCorner.family_cleared_parameter
#print axioms FourCorner.family_residue_quotient

namespace FourCorner
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

theorem family_padic_ratio {a b : ℤ} {t : ℚ}
    (htQ : t = (a : ℚ) / (b : ℚ))
    (ha : (a : ZMod 37) = 31) (hb : (b : ZMod 37) = 26) :
    ∃ h : ‖(t : ℚ_[37])‖ ≤ 1,
      padicResidue (t : ℚ_[37]) h = 14 := by
  let d : ℤ_[37] := (b : ℤ_[37])
  have hdr : PadicInt.toZMod d = 26 := by
    simpa only [d, map_intCast] using hb
  have hdn : ‖(b : ℚ_[37])‖ = 1 := by
    simpa only [d, PadicInt.coe_intCast] using
      padicInt_norm_coe_eq_one_of_residue_ne_zero d (by rw [hdr]; decide)
  have hd0 : (b : ℚ_[37]) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hdn
    norm_num at hdn
  have ht : (t : ℚ_[37]) = (a : ℚ_[37]) / (b : ℚ_[37]) := by
    exact_mod_cast htQ
  have hint : ‖(t : ℚ_[37])‖ ≤ 1 := by
    rw [ht, norm_div, hdn, div_one]
    exact Padic.norm_int_le_one (a)
  refine ⟨hint, ?_⟩
  have heq : padicIntegral (t : ℚ_[37]) hint * d = (a : ℤ_[37]) := by
    apply Subtype.ext
    simp only [PadicInt.coe_mul, padicIntegral_coe, d, PadicInt.coe_intCast]
    rw [ht, div_mul_cancel₀ _ hd0]
  have hr := congrArg PadicInt.toZMod heq
  rw [map_mul, hdr] at hr
  rw [map_intCast] at hr
  change padicResidue (t : ℚ_[37]) hint * 26 = (a : ZMod 37) at hr
  rw [ha] at hr
  apply mul_right_cancel₀ (by decide : (26 : ZMod 37) ≠ 0)
  have hnum : (14 : ZMod 37)*26=31 := by decide
  exact hr.trans hnum.symm

theorem family_padic_parameter (j : ℕ) (hj : 1 ≤ j) :
    ∃ h : ‖(commonFamilyT j : ℚ_[37])‖ ≤ 1,
      padicResidue (commonFamilyT j : ℚ_[37]) h = 14 :=
  family_padic_ratio (family_cleared_parameter j hj) (family_N_residue j) (family_D_residue j)

end FourCorner
#print axioms FourCorner.family_padic_parameter
namespace FourCorner

/-- Literal ordered real four-root source, with the strict return inequalities. -/
theorem real_source_strict {t : ℝ} (ht : 1 < t) (htop : t < Real.sqrt 5 / 2) :
    ∃ S : CommonRootSource ℝ t,
      t-1 < S.ell ∧ S.ell < t+1 ∧ 0 < S.P ∧ 0 < S.B ∧
        |S.P*S.M| + |S.B*S.C| < 2 := by
  let e := Real.sqrt (t^2-1)
  have hd : 0 < t^2-1 := by nlinarith
  have he : 0 < e := Real.sqrt_pos.mpr hd
  have heq : e^2 = t^2-1 := Real.sq_sqrt hd.le
  have hs : t-1 < e := by nlinarith
  have hT : e < t+1 := by nlinarith
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h5p := Real.sqrt_nonneg (5 : ℝ)
  have hehalf : e < 1/2 := by nlinarith
  let P := Real.sqrt (e+(t+1))
  let C := Real.sqrt (e-(t-1))
  let M := Real.sqrt ((t-1)*((t+1)-e)/e)
  let B := Real.sqrt ((t+1)*(e+(t-1))/e)
  have hp : 0 < e+(t+1) := by linarith
  have hc : 0 < e-(t-1) := by linarith
  have hm : 0 < (t-1)*((t+1)-e)/e :=
    div_pos (mul_pos (by linarith) (by linarith)) he
  have hb : 0 < (t+1)*(e+(t-1))/e :=
    div_pos (mul_pos (by linarith) (by linarith)) he
  have pp : 0 < P := Real.sqrt_pos.mpr hp
  have cp : 0 < C := Real.sqrt_pos.mpr hc
  have mp : 0 < M := Real.sqrt_pos.mpr hm
  have bp : 0 < B := Real.sqrt_pos.mpr hb
  have ps : P^2 = e+(t+1) := Real.sq_sqrt hp.le
  have cs : C^2 = e-(t-1) := Real.sq_sqrt hc.le
  have ms : M^2 = (t-1)*((t+1)-e)/e := Real.sq_sqrt hm.le
  have bs : B^2 = (t+1)*(e+(t-1))/e := Real.sq_sqrt hb.le
  have hpm : (P*M)^2 = 2*e := by
    rw [mul_pow, ps, ms]
    field_simp
    linear_combination -(t+1)*heq
  have hbc : (B*C)^2 = 2*e := by
    rw [mul_pow, bs, cs]
    field_simp
    linear_combination (t-1)*heq
  let S : CommonRootSource ℝ t := {
    ell := e, P := P, C := C, M := M, B := B
    t_ne_zero := by linarith
    t_ne_one := ne_of_gt ht
    t_ne_neg_one := by linarith
    ell_ne_zero := ne_of_gt he
    P_ne_zero := ne_of_gt pp
    C_ne_zero := ne_of_gt cp
    M_ne_zero := ne_of_gt mp
    B_ne_zero := ne_of_gt bp
    sqP := ps, sqC := cs, sqM := ms, sqB := bs }
  refine ⟨S, hs, hT, pp, bp, ?_⟩
  change |P*M| + |B*C| < 2
  rw [abs_of_pos (mul_pos pp mp), abs_of_pos (mul_pos bp cp)]
  have hpmpos := mul_pos pp mp
  have hbcpos := mul_pos bp cp
  have hpmone : P*M < 1 := by nlinarith
  have hbcone : B*C < 1 := by nlinarith
  linarith
end FourCorner
#print axioms FourCorner.real_source_strict
namespace FourCorner

theorem family_real_source (j : ℕ) (hj : 1 ≤ j) :
    ∃ S : CommonRootSource ℝ (commonFamilyT j : ℝ),
      (commonFamilyT j : ℝ)-1 < S.ell ∧ S.ell < (commonFamilyT j : ℝ)+1 ∧
      0 < S.P ∧ 0 < S.B ∧ |S.P*S.M|+|S.B*S.C|<2 := by
  have hb := family_parameter_bounds j hj
  apply real_source_strict
  · exact_mod_cast hb.1
  · have hq : (commonFamilyT j : ℝ) < ((17/16 : ℚ) : ℝ) := by exact_mod_cast hb.2
    norm_num at hq
    exact hq.trans family_upper_real
end FourCorner
#print axioms FourCorner.family_real_source
