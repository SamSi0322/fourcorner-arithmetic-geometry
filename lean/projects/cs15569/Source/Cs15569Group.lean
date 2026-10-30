import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Group
abbrev F := ZMod 113
instance : Fact (Nat.Prime 113) := ⟨by norm_num⟩
def curve : WeierstrassCurve.Affine F :=
  (⟨0,0,0,53,0⟩ : WeierstrassCurve F).toAffine
/-- Exact comparison with the manuscript's literal integral model. -/
theorem literal_model : curve =
    (⟨0,0,0,-(15569 : F)^2,0⟩ : WeierstrassCurve F).toAffine := by
  ext <;> decide
abbrev Pt := curve.Point

def A : Pt := .some 23 39 (by rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]; decide)
def A2 : Pt := .some 81 112 (by rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]; decide)
def A4 : Pt := .some 77 79 (by rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]; decide)
def T0 : Pt := .some 0 0 (by rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]; decide)
def B : Pt := .some 2 1 (by rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]; decide)
def B2 : Pt := .some 7 6 (by rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]; decide)
def Tplus : Pt := .some 88 0 (by rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]; decide)

theorem a_double : A + A = A2 := by
  rw [A, WeierstrassCurve.Affine.Point.add_self_of_Y_ne (by decide)]
  dsimp [A2]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope, curve, WeierstrassCurve.toAffine]
  simp only [show (39 : F) ≠ -39 by decide, if_false]
  rw [show (1640 / 78 : F) = 50 by
    apply (div_eq_iff (by decide)).mpr; decide]
  decide

theorem a2_double : A2 + A2 = A4 := by
  rw [A2, WeierstrassCurve.Affine.Point.add_self_of_Y_ne (by decide)]
  dsimp [A4]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope, curve, WeierstrassCurve.toAffine]
  simp only [show (112 : F) ≠ -112 by decide, if_false]
  rw [show (19736 / 224 : F) = 76 by
    apply (div_eq_iff (by decide)).mpr; decide]
  decide

theorem a4_double : A4 + A4 = T0 := by
  rw [A4, WeierstrassCurve.Affine.Point.add_self_of_Y_ne (by decide)]
  dsimp [T0]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope, curve, WeierstrassCurve.toAffine]
  simp only [show (79 : F) ≠ -79 by decide, if_false]
  rw [show (17840 / 158 : F) = 70 by
    apply (div_eq_iff (by decide)).mpr; decide]
  decide

theorem b_double : B + B = B2 := by
  rw [B, WeierstrassCurve.Affine.Point.add_self_of_Y_ne (by decide)]
  dsimp [B2]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope, curve, WeierstrassCurve.toAffine]
  simp only [show (1 : F) ≠ -1 by decide, if_false]
  rw [show (65 / 2 : F) = 89 by
    apply (div_eq_iff (by decide)).mpr; decide]
  decide

theorem b2_double : B2 + B2 = Tplus := by
  rw [B2, WeierstrassCurve.Affine.Point.add_self_of_Y_ne (by decide)]
  dsimp [Tplus]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope, curve, WeierstrassCurve.toAffine]
  simp only [show (6 : F) ≠ -6 by decide, if_false]
  rw [show (200 / 12 : F) = 92 by
    apply (div_eq_iff (by decide)).mpr; decide]
  decide

theorem t0_double : T0 + T0 = 0 := by
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  decide

theorem tplus_double : Tplus + Tplus = 0 := by
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  decide

theorem eight_A : 8 • A = T0 := by
  calc
    8 • A = 2 • (2 • (2 • A)) := by simp [smul_smul]
    _ = T0 := by simp only [two_nsmul, a_double, a2_double, a4_double]

theorem sixteen_A : 16 • A = 0 := by
  calc
    16 • A = 2 • (8 • A) := by simp [smul_smul]
    _ = 0 := by rw [eight_A, two_nsmul, t0_double]

theorem four_B : 4 • B = Tplus := by
  calc
    4 • B = 2 • (2 • B) := by simp [smul_smul]
    _ = Tplus := by simp only [two_nsmul, b_double, b2_double]

theorem eight_B : 8 • B = 0 := by
  calc
    8 • B = 2 • (4 • B) := by simp [smul_smul]
    _ = 0 := by rw [four_B, two_nsmul, tplus_double]

theorem exact_order_A : addOrderOf A = 16 := by
  apply addOrderOf_eq_prime_pow (p := 2) (n := 3)
  · simpa only [show 2 ^ 3 = (8 : ℕ) by decide, eight_A] using
      (show T0 ≠ 0 from WeierstrassCurve.Affine.Point.some_ne_zero _)
  · simpa using sixteen_A

theorem exact_order_B : addOrderOf B = 8 := by
  apply addOrderOf_eq_prime_pow (p := 2) (n := 2)
  · simpa only [show 2 ^ 2 = (4 : ℕ) by decide, four_B] using
      (show Tplus ≠ 0 from WeierstrassCurve.Affine.Point.some_ne_zero _)
  · simpa using eight_B

instance (x y : F) : Decidable (curve.Equation x y) :=
  decidable_of_iff _ (curve.equation_iff x y).symm

def finiteCurveDecidable (x y : F) : Decidable (curve.Nonsingular x y) :=
  decidable_of_iff _ (curve.nonsingular_iff x y).symm

instance (x y : F) : Decidable (curve.Nonsingular x y) := finiteCurveDecidable x y

/-- A complete count of all affine nonsingular pairs over F113. -/
theorem full_affine_count :
    Fintype.card {xy : F × F // curve.Nonsingular xy.1 xy.2} = 127 := by
  decide

/-- Cardinality of the actual nonsingular elliptic point group, including O. -/
theorem full_group_count : Nat.card Pt = 128 := by
  rw [Nat.card_congr curve.nonsingularPointEquiv]
  change Nat.card (Option {xy : F × F // curve.Nonsingular xy.1 xy.2}) = 128
  rw [Nat.card_eq_fintype_card, Fintype.card_option, full_affine_count]

theorem involutions_distinct : T0 ≠ Tplus := by
  intro h
  have hx := (WeierstrassCurve.Affine.Point.some.inj h).1
  exact (by decide : (0 : F) ≠ 88) hx

theorem involutions_sum_ne : T0 + Tplus ≠ 0 := by
  intro h
  have h' : T0 = Tplus := by
    have := congrArg (fun z : Pt => z + Tplus) h
    simpa only [add_assoc, tplus_double, add_zero, zero_add] using this
  exact involutions_distinct h'

private theorem coefficient_test :
    ∀ k : Fin 16, ∀ m : Fin 8, (k.val ≠ 0 ∨ m.val ≠ 0) →
      ∃ t : Fin 9,
        ((t.val * k.val) % 16 = 8 ∧ (t.val * m.val) % 8 = 0) ∨
        ((t.val * k.val) % 16 = 0 ∧ (t.val * m.val) % 8 = 4) ∨
        ((t.val * k.val) % 16 = 8 ∧ (t.val * m.val) % 8 = 4) := by decide

theorem coefficients_kernel (k : Fin 16) (m : Fin 8)
    (h : k.val • A + m.val • B = 0) : k.val = 0 ∧ m.val = 0 := by
  by_contra hn
  have hn' : k.val ≠ 0 ∨ m.val ≠ 0 := by omega
  obtain ⟨t, ht⟩ := coefficient_test k m hn'
  have hh := congrArg (fun z : Pt => t.val • z) h
  simp only [nsmul_add, ← mul_nsmul, nsmul_zero,
    Nat.mul_comm k.val t.val, Nat.mul_comm m.val t.val] at hh
  have ha (n : ℕ) : (n % 16) • A = n • A := by
    simpa only [exact_order_A] using mod_addOrderOf_nsmul A n
  have hb (n : ℕ) : (n % 8) • B = n • B := by
    simpa only [exact_order_B] using mod_addOrderOf_nsmul B n
  rw [← ha (t.val * k.val), ← hb (t.val * m.val)] at hh
  rcases ht with ⟨hka, hmb⟩ | ⟨hka, hmb⟩ | ⟨hka, hmb⟩
  · rw [hka, hmb, eight_A, zero_nsmul, add_zero] at hh
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ hh
  · rw [hka, hmb, zero_nsmul, four_B, zero_add] at hh
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ hh
  · rw [hka, hmb, eight_A, four_B] at hh
    exact involutions_sum_ne hh

def coefficientMap (km : Fin 16 × Fin 8) : Pt := km.1.val • A + km.2.val • B

theorem coefficientMap_injective : Function.Injective coefficientMap := by
  intro km lm heq
  let k := km.1.val + 16 - lm.1.val
  let m := km.2.val + 8 - lm.2.val
  have hk : k + lm.1.val = km.1.val + 16 := by dsimp [k]; omega
  have hm : m + lm.2.val = km.2.val + 8 := by dsimp [m]; omega
  have heq' : km.1.val • A + km.2.val • B = lm.1.val • A + lm.2.val • B := heq
  have hka : k • A + lm.1.val • A = km.1.val • A := by
    rw [← add_nsmul, hk, add_nsmul, sixteen_A, add_zero]
  have hmb : m • B + lm.2.val • B = km.2.val • B := by
    rw [← add_nsmul, hm, add_nsmul, eight_B, add_zero]
  have hzero : k • A + m • B = 0 := by
    rw [← hka, ← hmb] at heq'
    have : (k • A + m • B) + (lm.1.val • A + lm.2.val • B) =
        0 + (lm.1.val • A + lm.2.val • B) := by
      calc
        _ = (k • A + lm.1.val • A) + (m • B + lm.2.val • B) := by abel
        _ = _ := by simpa only [zero_add] using heq'
    exact add_right_cancel this
  have ha : (k % 16) • A = k • A := by
    simpa only [exact_order_A] using mod_addOrderOf_nsmul A k
  have hb : (m % 8) • B = m • B := by
    simpa only [exact_order_B] using mod_addOrderOf_nsmul B m
  rw [← ha, ← hb] at hzero
  obtain ⟨hkk, hmm⟩ := coefficients_kernel ⟨k % 16, Nat.mod_lt _ (by decide)⟩
    ⟨m % 8, Nat.mod_lt _ (by decide)⟩ hzero
  apply Prod.ext <;> apply Fin.ext
  · dsimp [k] at hkk
    have := km.1.isLt
    have := lm.1.isLt
    omega
  · dsimp [m] at hmm
    have := km.2.isLt
    have := lm.2.isLt
    omega

noncomputable instance : Fintype Pt :=
  Fintype.ofEquiv (Option {xy : F × F // curve.Nonsingular xy.1 xy.2})
    curve.nonsingularPointEquiv.symm

/-- Every actual finite-field point, with no sampled-subgroup replacement. -/
theorem coefficientMap_surjective : Function.Surjective coefficientMap := by
  apply (Fintype.bijective_iff_injective_and_card coefficientMap).mpr
    ⟨coefficientMap_injective, ?_⟩ |>.2
  have hc : Fintype.card Pt = 128 := by
    simpa only [Nat.card_eq_fintype_card] using full_group_count
  rw [hc]
  norm_num

/-- The exponent bound for the entire finite-field point group. -/
theorem whole_group_exponent (P : Pt) : 16 • P = 0 := by
  obtain ⟨⟨k,m⟩, rfl⟩ := coefficientMap_surjective P
  simp only [coefficientMap, nsmul_add]
  rw [smul_comm (16 : ℕ) k.val, sixteen_A, nsmul_zero]
  have h16B : 16 • B = 0 := by
    calc
      16 • B = 2 • (8 • B) := by simp [smul_smul]
      _ = 0 := by rw [eight_B, nsmul_zero]
  rw [smul_comm (16 : ℕ) m.val, h16B, nsmul_zero, add_zero]

/-- Thus eight annihilates the complete image of doubling. -/
theorem eight_annihilates_double (P : Pt) : 8 • (2 • P) = 0 := by
  simpa only [← mul_nsmul] using whole_group_exponent P

#print axioms literal_model
#print axioms coefficientMap_surjective
#print axioms eight_annihilates_double
#print axioms whole_group_exponent
#print axioms coefficients_kernel
#print axioms full_group_count
#print axioms a_double
#print axioms exact_order_A
#print axioms exact_order_B
end FourCorner.Cs15569Group
