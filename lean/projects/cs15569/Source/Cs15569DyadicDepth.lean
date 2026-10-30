import Cs15569DyadicGeneration

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section

private theorem double_coordinates {x y : ℚ}
    (h : CongruentEquation 15569 x y) (hy : y ≠ 0) :
    ∃ Y : ℚ, coordinates (2 • finitePoint (by norm_num) h) =
      some (((x^2+15569^2)^2/(4*y^2)),Y) := by
  have hyneg : y ≠ -y := by intro hz; apply hy; linarith
  rw [two_nsmul,finitePoint,WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (by simpa [WeierstrassCurve.Affine.negY,congruentCurve,WeierstrassCurve.toAffine] using hyneg)]
  refine ⟨(congruentCurve 15569).toAffine.addY x x y
    ((congruentCurve 15569).toAffine.slope x x y y),?_⟩
  simp only [coordinates,Option.some.injEq,Prod.mk.injEq]
  constructor
  · simp [WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY,congruentCurve,WeierstrassCurve.toAffine,hyneg]
    field_simp
    dsimp [CongruentEquation] at h
    linear_combination -32*x*h
  · trivial

/-- Multiplication by two maps every actual H point into E_3. This is a
coordinate proof with all depths and the point at infinity included. -/
theorem actual_double_deeper (Q : ActualH) :
    (2 • (Q:E)) ∈ Hlevel 15569 n15569_ne_zero 2 := by
  rcases Q with ⟨Q,hQ⟩
  cases Q with
  | zero =>
    change (2 • (0:E)) ∈ Hlevel 15569 n15569_ne_zero 2
    simp
  | some x y he =>
    have hE : CongruentEquation 15569 x y := (congruentEquation_iff_weierstrass _ _ _).mpr he.1
    have hxv := (some_mem_H_iff 15569 n15569_ne_zero x y he).mp hQ
    let chart := commonSourceDyadicOfRat 15569 x y hE hxv
    have hn : ‖(15569 : ℚ_[2])‖≤1 := Padic.norm_int_le_one 15569
    have hy : y ≠ 0 := by
      have hh := chart.y_ne_zero hn
      have hhy : (y : ℚ_[2]) ≠ 0 := hh
      exact_mod_cast hhy
    have hx : x ≠ 0 := by intro hz; simp [hz] at hxv
    have hm : x-15569 ≠ 0 := by
      have hh : (x : ℚ_[2])-(15569 : ℚ_[2]) ≠ 0 := by
        simpa [chart,commonSourceDyadicOfRat] using (chart.offsets_ne_zero hn).1
      exact_mod_cast hh
    have hp : x+15569 ≠ 0 := by
      have hh : (x : ℚ_[2])+(15569 : ℚ_[2]) ≠ 0 := by
        simpa [chart,commonSourceDyadicOfRat] using (chart.offsets_ne_zero hn).2
      exact_mod_cast hh
    have hvaly : 2*padicValRat 2 y=3*padicValRat 2 x := by
      have hh := chart.valuation_equation hn
      simpa [chart,commonSourceDyadicOfRat,Padic.valuation_ratCast] using hh
    have hnum : (x^2+15569^2 : ℚ) ≠ 0 := by positivity
    have hnumval : padicValRat 2 (x^2+15569^2)=2*padicValRat 2 x := by
      rw [padicValRat.add_eq_of_lt hnum (pow_ne_zero _ hx) (by norm_num)
        (by rw [padicValRat.pow,padicValRat.pow,val_n_two]; norm_num; omega),padicValRat.pow]
      norm_num
    have hfour : padicValRat 2 (4 : ℚ)=2 := by
      rw [show (4 : ℚ)=2^2 by norm_num,padicValRat.pow]
      have htwo : padicValRat 2 (2 : ℚ)=1 := by simpa only [Nat.cast_ofNat] using padicValRat.self (p:=2) (by norm_num)
      rw [htwo]
      norm_num
    have hnew : padicValRat 2 ((x^2+15569^2)^2/(4*y^2))=padicValRat 2 x-2 := by
      rw [padicValRat.div (pow_ne_zero _ hnum) (mul_ne_zero (by norm_num) (pow_ne_zero _ hy)),
        padicValRat.pow,padicValRat.mul (by norm_num) (pow_ne_zero _ hy),padicValRat.pow,hnumval,hfour]
      norm_num
      omega
    obtain ⟨Y,hcoords⟩ := double_coordinates hE hy
    have hfinite : (.some x y he : E)=finitePoint (by norm_num) hE := rfl
    rw [←hfinite] at hcoords
    cases hd : 2 • (.some x y he : E) with
    | zero =>
      rw [hd] at hcoords
      cases hcoords
    | some a b hab =>
      rw [hd] at hcoords
      simp only [coordinates,Option.some.injEq,Prod.mk.injEq] at hcoords
      rw [some_mem_Hlevel_iff]
      refine ⟨?_,?_⟩
      · rw [hcoords.1]
        exact div_ne_zero (pow_ne_zero _ hnum) (mul_ne_zero (by norm_num) (pow_ne_zero _ hy))
      · rw [hcoords.1,hnew]
        omega

/-- Complete H/2H generation and actual doubling depth force the whole H,
not just P and G, into the common depth-three formal neighborhood. -/
theorem actual_H_depth_three : ActualH ≤ Hlevel 15569 n15569_ne_zero 2 := by
  intro Q hQ
  obtain ⟨k,m,hk,hm,Z,hZ⟩ := actual_H_mod_two ⟨Q,hQ⟩
  have hP : P ∈ Hlevel 15569 n15569_ne_zero 2 := by
    rw [P,finitePoint,some_mem_Hlevel_iff]
    exact ⟨by norm_num [Cs15569Finite.px],by rw [P_depth]; norm_num⟩
  have hG : G ∈ Hlevel 15569 n15569_ne_zero 2 := by
    rw [G,finitePoint,some_mem_Hlevel_iff]
    exact ⟨by norm_num [Cs15569Finite.gx],by rw [G_depth]; norm_num⟩
  have hpoint := congrArg (fun Q : ActualH => (Q:E)) hZ
  change Q=k • G+m • P+2 • (Z:E) at hpoint
  rw [hpoint]
  exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _
    (AddSubgroup.nsmul_mem _ hG k) (AddSubgroup.nsmul_mem _ hP m)) (actual_double_deeper Z)

#print axioms actual_double_deeper
#print axioms actual_H_depth_three
end
end FourCorner.Cs15569Completion
