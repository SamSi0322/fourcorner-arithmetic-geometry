import Cs15569Reduction113
import Cs15569SourceTorsion
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section
abbrev F113 := ZMod 113
abbrev P113 := Cs15569Group.Pt

/-- Coordinates on the same actual finite elliptic-curve point group. -/
def coordinates113 : P113 → Option (F113 × F113)
  | .zero => none
  | .some x y _ => some (x,y)

theorem coordinates113_injective : Function.Injective coordinates113 := by
  intro Q R h
  cases Q <;> cases R <;> simp_all [coordinates113]

def abscissa113 (Q : P113) : Option F113 := (coordinates113 Q).map Prod.fst

theorem abscissa113_neg (Q : P113) : abscissa113 (-Q)=abscissa113 Q := by
  cases Q <;> rfl

/-- Coordinate compatibility with the canonical reduction of the same Q. -/
theorem coordinates113_reduce (Q : E) : coordinates113 (red113 Q)=
    residueCoordinates (reduce (q:=113) 15569 (by decide) (by decide) Q) :=
  by
    have hh := red113_coordinates_bridge Q
    cases hq : red113 Q with
    | zero => rw [hq] at hh; exact hh
    | some x y he => rw [hq] at hh; exact hh

def g113 : ZMod 8 →+ P113 := ZMod.lift 8 ⟨zmultiplesHom P113 Cs15569Group.A2,by
  change (8 : ℤ) • Cs15569Group.A2=0
  exact (natCast_zsmul Cs15569Group.A2 8).trans g113_eight_zero⟩

def t113 : ZMod 2 →+ P113 := ZMod.lift 2 ⟨zmultiplesHom P113 Cs15569Group.Tplus,by
  change (2 : ℤ) • Cs15569Group.Tplus=0
  exact (natCast_zsmul Cs15569Group.Tplus 2).trans (by simpa only [two_nsmul] using Cs15569Group.tplus_double)⟩

theorem g113_nat (k : ℕ) : g113 k=k • Cs15569Group.A2 := by
  have hh := ZMod.lift_coe 8
    (⟨zmultiplesHom P113 Cs15569Group.A2,by
      change (8 : ℤ) • Cs15569Group.A2=0
      exact (natCast_zsmul Cs15569Group.A2 8).trans g113_eight_zero⟩) (k : ℤ)
  simpa only [g113,Int.cast_natCast,zmultiplesHom_apply,natCast_zsmul] using hh

theorem t113_nat (k : ℕ) : t113 k=k • Cs15569Group.Tplus := by
  have hh := ZMod.lift_coe 2
    (⟨zmultiplesHom P113 Cs15569Group.Tplus,by
      change (2 : ℤ) • Cs15569Group.Tplus=0
      exact (natCast_zsmul Cs15569Group.Tplus 2).trans (by simpa only [two_nsmul] using Cs15569Group.tplus_double)⟩) (k : ℤ)
  simpa only [t113,Int.cast_natCast,zmultiplesHom_apply,natCast_zsmul] using hh

private theorem g113_four : g113 4=Cs15569Group.T0 := by
  have hh : 4 • Cs15569Group.A2=Cs15569Group.T0 := by
    calc
      4 • Cs15569Group.A2=2 • (2 • Cs15569Group.A2) := by simp only [smul_smul]; rfl
      _ = 2 • Cs15569Group.A4 := by
        have ht : 2 • Cs15569Group.A2=Cs15569Group.A4 := by
          rw [two_nsmul,Cs15569Group.a2_double]
        rw [ht]
      _ = Cs15569Group.T0 := by rw [two_nsmul,Cs15569Group.a4_double]
  simpa only [Nat.cast_ofNat] using (g113_nat 4).trans hh

private theorem add_point_certificate {x₁ y₁ x₂ y₂ x₃ y₃ s : F113}
    (h₁ : Cs15569Group.curve.Nonsingular x₁ y₁)
    (h₂ : Cs15569Group.curve.Nonsingular x₂ y₂)
    (h₃ : Cs15569Group.curve.Nonsingular x₃ y₃)
    (hx : x₁ ≠ x₂) (hs : (y₁-y₂)/(x₁-x₂)=s)
    (hxx : s^2-x₁-x₂=x₃) (hyy : -(s*(x₃-x₁)+y₁)=y₃) :
    (.some x₁ y₁ h₁ : P113)+.some x₂ y₂ h₂=.some x₃ y₃ h₃ := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx,WeierstrassCurve.Affine.Point.some.injEq]
  simp only [WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope_of_X_ne hx,Cs15569Group.curve,WeierstrassCurve.toAffine,
    zero_mul,add_zero,sub_zero,hs,hxx]
  exact ⟨trivial,hyy⟩

def g3_113 : P113 := .some 16 57 (by
  rw [WeierstrassCurve.Affine.nonsingular_iff,WeierstrassCurve.Affine.equation_iff]
  decide)
def gt_113 : P113 := .some 87 97 (by
  rw [WeierstrassCurve.Affine.nonsingular_iff,WeierstrassCurve.Affine.equation_iff]
  decide)
def g3t_113 : P113 := .some 11 85 (by
  rw [WeierstrassCurve.Affine.nonsingular_iff,WeierstrassCurve.Affine.equation_iff]
  decide)

private theorem actual_g_three : g113 3=g3_113 := by
  have hh : g113 3=Cs15569Group.A2+Cs15569Group.A4 := by
    rw [show (3 : ZMod 8)=1+(1+1) by decide,map_add,map_add]
    have h1 : g113 1=Cs15569Group.A2 := by simpa using g113_nat 1
    rw [h1,Cs15569Group.a2_double]
  rw [hh,Cs15569Group.A2,Cs15569Group.A4,g3_113]
  apply add_point_certificate (s:=93) _ _ _ (by decide)
  · apply (div_eq_iff (by decide)).mpr
    decide
  · decide
  · decide

private theorem actual_g_plus : g113 1+t113 1=gt_113 := by
  have h1 : g113 1=Cs15569Group.A2 := by simpa using g113_nat 1
  have ht : t113 1=Cs15569Group.Tplus := by simpa using t113_nat 1
  rw [h1,ht,Cs15569Group.A2,Cs15569Group.Tplus,gt_113]
  apply add_point_certificate (s:=97) _ _ _ (by decide)
  · apply (div_eq_iff (by decide)).mpr
    decide
  · decide
  · decide

private theorem actual_g_three_plus : g113 3+t113 1=g3t_113 := by
  have ht : t113 1=Cs15569Group.Tplus := by simpa using t113_nat 1
  rw [actual_g_three,ht,g3_113,Cs15569Group.Tplus,g3t_113]
  apply add_point_certificate (s:=51) _ _ _ (by decide)
  · apply (div_eq_iff (by decide)).mpr
    decide
  · decide
  · decide

/-- Complete odd coefficient image, with torsion parity retained. -/
private theorem odd_abscissa_table (a : ZMod 8) (b : ZMod 2)
    (ha : (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) a=1) :
    (abscissa113 (g113 (a+4)+t113 (b+1)),abscissa113 (g113 a+t113 b))=
      (some 11,some 81) ∨
    (abscissa113 (g113 (a+4)+t113 (b+1)),abscissa113 (g113 a+t113 b))=
      (some 16,some 87) ∨
    (abscissa113 (g113 (a+4)+t113 (b+1)),abscissa113 (g113 a+t113 b))=
      (some 81,some 11) ∨
    (abscissa113 (g113 (a+4)+t113 (b+1)),abscissa113 (g113 a+t113 b))=
      (some 87,some 16) := by
  have h1 : g113 1=Cs15569Group.A2 := by simpa using g113_nat 1
  have h5 : g113 5= -g3_113 := by rw [show (5 : ZMod 8)= -3 by decide,map_neg,actual_g_three]
  have h7 : g113 7= -Cs15569Group.A2 := by rw [show (7 : ZMod 8)= -1 by decide,map_neg,h1]
  have h5t : g113 5+t113 1= -g3t_113 := by
    rw [show (5 : ZMod 8)= -3 by decide,map_neg]
    have ht : t113 1= -t113 1 := by
      rw [←map_neg]
      congr 1
    rw [ht,←neg_add,actual_g_three_plus]
  have h7t : g113 7+t113 1= -gt_113 := by
    rw [show (7 : ZMod 8)= -1 by decide,map_neg]
    have ht : t113 1= -t113 1 := by
      rw [←map_neg]
      congr 1
    rw [ht,←neg_add,actual_g_plus]
  have hca : ∀ a : ZMod 8, (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) a=1 →
      a=1 ∨ a=3 ∨ a=5 ∨ a=7 := by decide
  have hcb : ∀ b : ZMod 2, b=0 ∨ b=1 := by decide
  rcases hca a ha with rfl | rfl | rfl | rfl <;> rcases hcb b with rfl | rfl
  all_goals simp only [show (1+4 : ZMod 8)=5 by decide,
    show (3+4 : ZMod 8)=7 by decide,show (5+4 : ZMod 8)=1 by decide,
    show (7+4 : ZMod 8)=3 by decide,show (0+1 : ZMod 2)=1 by decide,
    show (1+1 : ZMod 2)=0 by decide,map_zero,add_zero]
  all_goals try rw [h5t]
  all_goals try rw [h7t]
  all_goals try rw [actual_g_plus]
  all_goals try rw [actual_g_three_plus]
  all_goals simp only [h5,h7,h1,actual_g_three,abscissa113,
    coordinates113,g3_113,gt_113,g3t_113,Cs15569Group.A2]
  all_goals decide

theorem g113_four_eq_T0 : g113 4=Cs15569Group.T0 := g113_four

theorem full_odd_abscissa_table (a : ZMod 8) (b : ZMod 2)
    (ha : (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) a=1) :
    (abscissa113 (g113 (a+4)+t113 (b+1)),abscissa113 (g113 a+t113 b))=
      (some 11,some 81) ∨
    (abscissa113 (g113 (a+4)+t113 (b+1)),abscissa113 (g113 a+t113 b))=
      (some 16,some 87) ∨
    (abscissa113 (g113 (a+4)+t113 (b+1)),abscissa113 (g113 a+t113 b))=
      (some 81,some 11) ∨
    (abscissa113 (g113 (a+4)+t113 (b+1)),abscissa113 (g113 a+t113 b))=
      (some 87,some 16) := odd_abscissa_table a b ha

#print axioms coordinates113_reduce
#print axioms actual_g_three
#print axioms actual_g_plus
#print axioms actual_g_three_plus
#print axioms odd_abscissa_table
end
end FourCorner.Cs15569Completion
