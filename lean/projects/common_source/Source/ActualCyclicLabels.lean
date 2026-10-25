import OddKummerSpecialization

noncomputable section
namespace FourCorner.CommonSource
open OrderedSplit
variable {q : ℕ} [Fact q.Prime]

private theorem curve_eq_half_zero_square {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve.Affine K) (n : K) (hn : n ≠ 0)
    (hW : W=(OverField.curve n).toAffine) (x y : K)
    (hxy : W.Nonsingular x y) (hzero : W.Nonsingular 0 0)
    (hd : 2 • (WeierstrassCurve.Affine.Point.some x y hxy : W.Point)=
      WeierstrassCurve.Affine.Point.some 0 0 hzero) : (x/n)^2= -1 := by
  subst W
  exact OverField.normalized_x_square_of_double hn hxy hd

private theorem curve_eq_half_zero_order {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve.Affine K) (n : K) (hn : n ≠ 0)
    (hW : W=(OverField.curve n).toAffine) (A : W.Point)
    (hzero : W.Nonsingular 0 0)
    (hd : 2 • A=WeierstrassCurve.Affine.Point.some 0 0 hzero) : addOrderOf A=4 := by
  subst W
  exact OverField.addOrderOf_eq_four_of_double hn hd

/-- Order four of the genuine reduced generator follows from 2A=T0. -/
theorem residue_half_zero_order {n : ℤ} (hnq : (n:ZMod q) ≠ 0)
    (A : ResiduePoint n q) (hd : 2 • A=residueT0 n hnq) : addOrderOf A=4 := by
  exact curve_eq_half_zero_order (residueCurve n q) (n:ZMod q) hnq
    (residueCurve_eq_fieldCurve n) A _ hd

/-- A half of the actual marked T0 has a finite abscissa n*i, where i²=-1.
No coordinates or choice of i are supplied as extra assumptions. -/
theorem residue_half_zero_coordinates {n : ℤ} (hnq : (n:ZMod q) ≠ 0)
    (A : ResiduePoint n q) (hd : 2 • A=residueT0 n hnq) :
    ∃ i b : ZMod q, i^2= -1 ∧ residueCoordinates A=some ((n:ZMod q)*i,b) := by
  cases A with
  | zero =>
    change 2 • (0:ResiduePoint n q)=residueT0 n hnq at hd
    have hz : (0:ResiduePoint n q)=residueT0 n hnq := by simpa using hd
    have hc := congrArg residueCoordinates hz
    cases hc
  | some x y hxy =>
    have hi := curve_eq_half_zero_square (residueCurve n q) (n:ZMod q) hnq
      (residueCurve_eq_fieldCurve n) x y hxy _ hd
    refine ⟨x/(n:ZMod q),y,hi,?_⟩
    change some (x,y)=some ((n:ZMod q)*(x/(n:ZMod q)),y)
    congr 2
    field_simp

/-- The two odd labels of a true order-four cyclic subgroup retain the same
abscissa. The ordinate may change sign and is retained as an actual coordinate. -/
theorem cyclic_odd_abscissa {n : ℤ} (A : ResiduePoint n q) (hA : addOrderOf A=4)
    {x y : ZMod q} (hxy : residueCoordinates A=some (x,y))
    (r : ZMod 4) (hr : r=1 ∨ r=3) :
    ∃ b : ZMod q, residueCoordinates (Slot14.coordinate A hA r : ResiduePoint n q)=some (x,b) := by
  rcases hr with rfl | rfl
  · exact ⟨y,by simpa only [Slot14.coordinate_one] using hxy⟩
  · have hthree : (3:ZMod 4)= -1 := by decide
    have he : (Slot14.coordinate A hA 3 : ResiduePoint n q)= -A := by
      rw [hthree,map_neg,AddSubgroup.coe_neg,Slot14.coordinate_one]
    rw [he]
    cases A with
    | zero => cases hxy
    | some u v hu =>
      have hv : u=x ∧ v=y := by simpa only [residueCoordinates,Option.some.injEq,Prod.mk.injEq] using hxy
      refine ⟨(residueCurve n q).negY u v,?_⟩
      simp only [WeierstrassCurve.Affine.Point.neg_some,residueCoordinates,hv.1]

/-- For the actual whole-H reduction character, odd labels force the literal
n*i abscissa, with i determined by the same generator. -/
theorem actual_phi_odd_abscissa {n : ℤ} (hn : n ≠ 0)
    (hq2 : q ≠ 2) (hnq : (n:ZMod q) ≠ 0)
    (A : ResiduePoint n q) (hA : addOrderOf A=4)
    (hwhole : ∀ P : H n hn, reduce n hq2 hnq P ∈ AddSubgroup.zmultiples A)
    {i b : ZMod q} (hxy : residueCoordinates A=some ((n:ZMod q)*i,b))
    (P : H n hn)
    (hodd : Slot14.phi (H n hn) hq2 hnq A hA hwhole P=1 ∨
      Slot14.phi (H n hn) hq2 hnq A hA hwhole P=3) :
    ∃ y : ZMod q, residueCoordinates (reduce n hq2 hnq P)=some ((n:ZMod q)*i,y) := by
  rw [← Slot14.phi_spec (H n hn) hq2 hnq A hA hwhole P]
  exact cyclic_odd_abscissa A hA hxy _ hodd

/-- A locally square actual global first Kummer slot forces the actual cyclic
reduction label to be even. This proves the W-parity step of the odd probe. -/
theorem actual_phi_even_of_first_slot {n : ℤ} (hn : n ≠ 0)
    (hq : q%8=5) (hnq : (n:ZMod q) ≠ 0) (hns : IsSquare (n:ℚ_[q]))
    (A : ResiduePoint n q) (hA : addOrderOf A=4)
    (hd : 2 • A=residueT0 n hnq)
    (hwhole : ∀ P : H n hn, reduce n (by omega : q≠2) hnq P ∈ AddSubgroup.zmultiples A)
    (P : H n hn) (d : ℚ) (hd0 : d ≠ 0)
    (hclass : kummerDelta (n:ℚ) (by exact_mod_cast hn) (Multiplicative.ofAdd (P:Point (n:ℚ))) 0=
      scalarClass d hd0) (hds : IsSquare (d:ℚ_[q])) :
    Slot14.phi (H n hn) (by omega : q≠2) hnq A hA hwhole P=0 ∨
    Slot14.phi (H n hn) (by omega : q≠2) hnq A hA hwhole P=2 := by
  obtain ⟨i,b,hi,hxy⟩ := residue_half_zero_coordinates hnq A hd
  have hnres : IsSquare (n:ZMod q) := by
    have hs := padicInt_isSquare_toZMod_of_isSquare_coe (n:ℤ_[q]) hns
    simpa using hs
  have hnot := csOdd_ni_nonsquare hq hnq hnres hi
  have hnotodd : ¬ (Slot14.phi (H n hn) (by omega : q≠2) hnq A hA hwhole P=1 ∨
      Slot14.phi (H n hn) (by omega : q≠2) hnq A hA hwhole P=3) := by
    intro hh
    obtain ⟨y,hy⟩ := actual_phi_odd_abscissa hn (by omega) hnq A hA hwhole hxy P hh
    exact hnot (H_first_slot_reduction_square q hn (by omega) hnq P d hd0 hclass hds _ _ hy)
  have finite_labels : ∀ r : ZMod 4, ¬(r=1 ∨ r=3) → r=0 ∨ r=2 := by decide
  exact finite_labels _ hnotodd

#print axioms residue_half_zero_order
#print axioms residue_half_zero_coordinates
#print axioms cyclic_odd_abscissa
#print axioms actual_phi_even_of_first_slot
end FourCorner.CommonSource
