import Cs15569DyadicSquareEight
import Cs15569ThreeReduction

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section

/-- Oddness of the actual z/8 residue means exact depth3, at the same finite
rational point. The formal parameter is never chosen independently. -/
theorem coefficient_odd_depth_three (Q : ActualH) {x y : ℚ}
    (he : (congruentCurve 15569).toAffine.Nonsingular x y) (hQ : (Q:E)=.some x y he)
    {Z : ActualH} {k m : ℕ} (hrep : Q=k • HG+m • HP+8 • Z)
    (_hk : k<8) (_hm : m<8) (hkodd : k%2=1) : padicValRat 2 x= -6 := by
  let a := usualScaledParameter 15569 n15569_ne_zero 2 (toLevelThree Q)
  have hcast : (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) (PadicInt.toZModPow 3 a)=
      PadicInt.toZModPow 1 a := by
    simpa only [ZMod.castHom_apply] using PadicInt.cast_toZModPow (p:=2) 1 3 (by decide) a
  have hparity : (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) (7*k+6*m)=1 := by
    simp only [map_add,map_mul,map_natCast,map_ofNat]
    rw [show (7 : ZMod 2)=1 by decide,show (6 : ZMod 2)=0 by decide,one_mul,zero_mul,add_zero]
    have hh : (k : ZMod 2)=(k%2 : ℕ) := (ZMod.natCast_mod k 2).symm
    rw [hh,hkodd]
    norm_num
  have hres : PadicInt.toZModPow 1 a ≠ 0 := by
    rw [←hcast]
    have hformula : phiEight Q=PadicInt.toZModPow 3 a := phiEight_formula Q
    rw [←hformula,phiEight_mod_eight hrep,hparity]
    decide
  have hanInt : a ≠ 0 := by
    intro hz
    apply hres
    rw [hz,map_zero]
  have havInt : a.valuation=0 := by
    have hh := commonSource_residue_zero_iff_depth a hanInt 1
    by_contra hv
    have hvpos : 1≤a.valuation := by omega
    exact hres (hh.mpr hvpos)
  have hav : (a : ℚ_[2]).valuation=0 := by
    rw [PadicInt.valuation_coe,havInt]
    norm_num
  have hmem := Q.property
  rw [hQ] at hmem
  have hxv := (some_mem_H_iff 15569 n15569_ne_zero x y he).mp hmem
  have hE : CongruentEquation 15569 x y := (congruentEquation_iff_weierstrass _ _ _).mpr he.1
  let chart := commonSourceDyadicOfRat 15569 x y hE hxv
  have hn : ‖(15569 : ℚ_[2])‖≤1 := Padic.norm_int_le_one 15569
  have hparam : (a : ℚ_[2])=chart.z/8 := by
    simpa [a,chart,commonSourceDyadicOfRat,CommonSourceDyadicPoint.z] using phiEight_parameter Q he hQ
  have h8 : (8 : ℚ_[2]).valuation=3 := by
    rw [show (8 : ℚ_[2])=2^3 by norm_num,Padic.valuation_pow]
    have h2 : (2 : ℚ_[2]).valuation=1 := by simpa only [Nat.cast_ofNat] using Padic.valuation_p (p:=2)
    rw [h2]
    norm_num
  have hvp := congrArg Padic.valuation hparam
  rw [commonRoot_val_div (chart.z_ne_zero hn) (by norm_num),h8,hav,chart.valuation_z hn] at hvp
  have hdepth := (chart.depth_spec hn).2.1
  have hdepth' : padicValRat 2 x= -2*(chart.depth : ℤ) := by
    simpa [chart,commonSourceDyadicOfRat,Padic.valuation_ratCast] using hdepth
  omega

/-- Combining the actual local3 square with the actual local2 square gives
the manuscript's sign match on the same complete mod8 source coefficients. -/
theorem actual_source_mod_eight_sign (S : ActualPair 15569 n15569_ne_zero) (r : S.Remainders)
    {Z Z' : ActualH} {k m k' m' : ℕ}
    (hU : S.U=k • HG+m • HP+8 • Z) (hV : S.V=k' • HG+m' • HP+8 • Z')
    (hk : k<8) (hm : m<8) (hk' : k'<8) (hm' : m'<8)
    (hs2 : IsSquare (commonSourceReturn (15569 : ℚ_[2]) S.a S.c))
    (hs3 : IsSquare (commonSourceReturn (15569 : ℚ_[3]) S.a S.c)) :
    k%2=1 ∧ k'%2=1 ∧
      ((7*k+6*m : ZMod 8)=(7*k'+6*m' : ZMod 8) ∨
        (7*k+6*m : ZMod 8)= -(7*k'+6*m' : ZMod 8)) := by
  obtain ⟨hko,hk'o⟩ := three_forces_odd_coefficients S r hU hV hs3
  have hx := coefficient_odd_depth_three S.U (nonsingular (by norm_num) r.hU) r.eqU hU hk hm hko
  have hw := coefficient_odd_depth_three S.V (nonsingular (by norm_num) r.hV) r.eqV hV hk' hm' hk'o
  have hsign := actual_depth_three_square_sign S r hx hw hs2
  rw [phiEight_mod_eight hU,phiEight_mod_eight hV] at hsign
  exact ⟨hko,hk'o,hsign⟩

#print axioms coefficient_odd_depth_three
#print axioms actual_source_mod_eight_sign
end
end FourCorner.Cs15569Completion
