import Cs15569DyadicCharacterEight
import ActualBranch15569

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section

private theorem scaled_abscissa_integral {x : ℚ} (hx : padicValRat 2 x= -6) :
    ∃ q : ℤ_[2], (q : ℚ_[2])=64*(x : ℚ_[2]) ∧ (q : ℚ_[2]).valuation=0 := by
  have hxn : x ≠ 0 := by intro hz; simp [hz] at hx
  have h64 : (64 : ℚ_[2]).valuation=6 := by
    rw [show (64 : ℚ_[2])=2^6 by norm_num,Padic.valuation_pow]
    have htwo : (2 : ℚ_[2]).valuation=1 := by simpa only [Nat.cast_ofNat] using Padic.valuation_p (p:=2)
    rw [htwo]
    norm_num
  have hv : (64*(x : ℚ_[2])).valuation=0 := by
    rw [Padic.valuation_mul (by norm_num) (by exact_mod_cast hxn),h64,Padic.valuation_ratCast,hx]
    norm_num
  have hn : ‖64*(x : ℚ_[2])‖≤1 := (Padic.norm_le_one_iff_val_nonneg _).mpr (by omega)
  exact ⟨⟨64*(x : ℚ_[2]),hn⟩,rfl,hv⟩

private theorem parameter_abscissa_mod_sixteen (Q : ActualH) {x y : ℚ}
    (he : (congruentCurve 15569).toAffine.Nonsingular x y)
    (hQ : (Q:E)=.some x y he) (q : ℤ_[2]) (hq : (q : ℚ_[2])=64*(x : ℚ_[2])) :
    let a := usualScaledParameter 15569 n15569_ne_zero 2 (toLevelThree Q)
    PadicInt.toZModPow 4 q*(PadicInt.toZModPow 4 a)^2=(1 : ZMod 16) := by
  let a := usualScaledParameter 15569 n15569_ne_zero 2 (toLevelThree Q)
  have ha : (a : ℚ_[2])=(-(x : ℚ_[2])/y)/8 := phiEight_parameter Q he hQ
  have hmem := Q.property
  rw [hQ] at hmem
  have hxv := (some_mem_H_iff 15569 n15569_ne_zero x y he).mp hmem
  have hE : CongruentEquation 15569 x y := (congruentEquation_iff_weierstrass _ _ _).mpr he.1
  let chart := commonSourceDyadicOfRat 15569 x y hE hxv
  have hn : ‖(15569 : ℚ_[2])‖≤1 := Padic.norm_int_le_one 15569
  have hxn : (x : ℚ_[2]) ≠ 0 := chart.x_ne_zero
  have hyn : (y : ℚ_[2]) ≠ 0 := chart.y_ne_zero hn
  have ht := chart.norm_n_div_x_le hn
  have hi : ‖((15569 : ℚ_[2])/x)^2‖≤(1 : ℝ)/256 := by
    rw [norm_pow]
    have hh := pow_le_pow_left₀ (norm_nonneg ((15569 : ℚ_[2])/x)) ht 2
    norm_num at hh ⊢
    exact hh
  let I : ℤ_[2] := ⟨((15569 : ℚ_[2])/x)^2,by linarith⟩
  have hIr : PadicInt.toZModPow 4 I=(0 : ZMod 16) := by
    apply (dyadic_residue_zero_iff_norm_le I 4).mpr
    change ‖((15569 : ℚ_[2])/x)^2‖≤_
    rw [show (2 : ℝ)^(-((4 : ℕ) : ℤ))=(1 : ℝ)/16 by norm_num]
    exact le_trans hi (by norm_num)
  have heq : q*a^2*(1-I)=(1 : ℤ_[2]) := by
    apply PadicInt.ext
    simp only [PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_sub,PadicInt.coe_one]
    rw [hq,ha]
    change (64*(x : ℚ_[2]))*((-(x : ℚ_[2])/y)/8)^2*(1-((15569 : ℚ_[2])/x)^2)=1
    have hc : (y : ℚ_[2])^2=(x : ℚ_[2])*((x : ℚ_[2])-15569)*((x : ℚ_[2])+15569) := by
      exact_mod_cast hE
    field_simp [hxn,hyn]
    linear_combination -64*hc
  have hr := congrArg (PadicInt.toZModPow 4) heq
  simp only [map_mul,map_pow,map_sub,map_one,hIr,sub_zero,mul_one] at hr
  exact hr

private theorem average_square (S : ActualPair 15569 n15569_ne_zero) (r : S.Remainders)
    (hs : IsSquare (commonSourceReturn (15569 : ℚ_[2]) S.a S.c)) :
    IsSquare (((r.x : ℚ_[2])+(r.w : ℚ_[2]))/2) := by
  have ho := actual_pair_unique_branch S r
  have ha : (S.a : ℚ_[2])=commonSourceTranslateMinus (15569 : ℚ_[2]) r.x := by
    dsimp [commonSourceTranslateMinus] at ho ⊢
    exact_mod_cast ho.1
  have hc : (S.c : ℚ_[2])=commonSourceTranslatePlus (15569 : ℚ_[2]) r.w := by
    dsimp [commonSourceTranslatePlus] at ho ⊢
    exact_mod_cast ho.2
  have hxv := (some_mem_H_iff 15569 n15569_ne_zero r.x r.y (nonsingular (by norm_num) r.hU)).mp r.memU
  have hwv := (some_mem_H_iff 15569 n15569_ne_zero r.w r.z (nonsingular (by norm_num) r.hV)).mp r.memV
  let U := commonSourceDyadicOfRat 15569 r.x r.y r.hU hxv
  let V := commonSourceDyadicOfRat 15569 r.w r.z r.hV hwv
  have hn : ‖(15569 : ℚ_[2])‖≤1 := Padic.norm_int_le_one 15569
  have hns : IsSquare (15569 : ℚ_[2]) := by
    simpa only [Int.cast_ofNat] using dyadic_square_of_int_mod_eight 15569 (by decide)
  have hfactor := ((V.local_squares hn).1.mul (U.local_squares hn).2.2).div hns
  have hsq := hs.mul hfactor
  have hid : commonSourceReturn (15569 : ℚ_[2]) S.a S.c*
      ((r.w : ℚ_[2])*((r.x : ℚ_[2])+15569)/15569)=((r.x : ℚ_[2])+(r.w : ℚ_[2]))/2 := by
    have hvn : (r.w : ℚ_[2]) ≠ 0 := V.x_ne_zero
    have hup : (r.x : ℚ_[2])+15569 ≠ 0 := by
      simpa [U,commonSourceDyadicOfRat] using (U.offsets_ne_zero hn).2
    have hwm : (r.w : ℚ_[2])-15569 ≠ 0 := by
      simpa [V,commonSourceDyadicOfRat] using (V.offsets_ne_zero hn).1
    have hf := commonSource_return_minus_plus (n:=(15569 : ℚ_[2])) (u:=(r.x : ℚ_[2]))
      (v:=(r.w : ℚ_[2])) (by norm_num) hvn hup hwm
    rw [ha,hc,hf]
    field_simp [hvn,hup]
  have hsq' : IsSquare (commonSourceReturn (15569 : ℚ_[2]) S.a S.c*
      ((r.w : ℚ_[2])*((r.x : ℚ_[2])+15569)/15569)) := by
    simpa [U,V,commonSourceDyadicOfRat] using hsq
  exact hid ▸ hsq' 

/-- The actual square return at2 imposes the stronger sign match modulo8
when the SAME remainders have depth exactly3. No residue premise replaces
squareness of the original literal return. -/
theorem actual_depth_three_square_sign (S : ActualPair 15569 n15569_ne_zero) (r : S.Remainders)
    (hx : padicValRat 2 r.x= -6) (hw : padicValRat 2 r.w= -6)
    (hs : IsSquare (commonSourceReturn (15569 : ℚ_[2]) S.a S.c)) :
    phiEight S.U=phiEight S.V ∨ phiEight S.U= -phiEight S.V := by
  let a := usualScaledParameter 15569 n15569_ne_zero 2 (toLevelThree S.U)
  let b := usualScaledParameter 15569 n15569_ne_zero 2 (toLevelThree S.V)
  obtain ⟨q,hq,hqv⟩ := scaled_abscissa_integral hx
  obtain ⟨p,hp,hpv⟩ := scaled_abscissa_integral hw
  have ha := parameter_abscissa_mod_sixteen S.U (nonsingular (by norm_num) r.hU) r.eqU q hq
  have hb := parameter_abscissa_mod_sixteen S.V (nonsingular (by norm_num) r.hV) r.eqV p hp
  have hxreal := depth_two_real_identity r.hU (by omega : padicValRat 2 r.x≤ -4)
  have hwreal := depth_two_real_identity r.hV (by omega : padicValRat 2 r.w≤ -4)
  have hsum : (q : ℚ_[2])+(p : ℚ_[2]) ≠ 0 := by
    rw [hq,hp,←mul_add]
    apply mul_ne_zero (by norm_num)
    exact_mod_cast (show r.x+r.w ≠ 0 by linarith)
  have hqn : (q : ℚ_[2]) ≠ 0 := by
    rw [hq]
    apply mul_ne_zero (by norm_num)
    exact_mod_cast (show r.x ≠ 0 by linarith)
  have hpn : (p : ℚ_[2]) ≠ 0 := by
    rw [hp]
    apply mul_ne_zero (by norm_num)
    exact_mod_cast (show r.w ≠ 0 by linarith)
  have hsumv := commonRoot_dyadic_unit_add_pos hqn hpn hqv hpv hsum
  have hhv : 0≤(((q : ℚ_[2])+(p : ℚ_[2]))/2).valuation := by
    rw [commonRoot_val_div hsum (by norm_num),commonSource_dyadic_val_two]
    omega
  let H : ℤ_[2] := ⟨((q : ℚ_[2])+(p : ℚ_[2]))/2,(Padic.norm_le_one_iff_val_nonneg _).mpr hhv⟩
  have hHsq : IsSquare H := by
    apply (padicInt_isSquare_coe_iff H).mp
    have hh := (average_square S r hs).mul (IsSquare.sq (8 : ℚ_[2]))
    have hHeqfield : (H : ℚ_[2])=(((r.x : ℚ_[2])+(r.w : ℚ_[2]))/2)*8^2 := by
      change ((q : ℚ_[2])+(p : ℚ_[2]))/2=(((r.x : ℚ_[2])+(r.w : ℚ_[2]))/2)*8^2
      rw [hq,hp]
      ring
    rw [hHeqfield]
    exact hh
  have hHeq : 2*H=q+p := by
    apply PadicInt.ext
    change 2*(((q : ℚ_[2])+(p : ℚ_[2]))/2)=(q : ℚ_[2])+(p : ℚ_[2])
    ring
  have hHr := congrArg (PadicInt.toZModPow 4) hHeq
  simp only [map_mul,map_add,map_ofNat] at hHr
  have hfinite_unit : ∀ A Q : ZMod 16, Q*A^2=1 → Q=A^2 ∧ A^4=1 := by decide
  obtain ⟨hqa,ha4⟩ := hfinite_unit _ _ ha
  obtain ⟨hpb,hb4⟩ := hfinite_unit _ _ hb
  rw [hqa,hpb] at hHr
  have hfinite_sign : ∀ A B H : ZMod 16, A^4=1 → B^4=1 → 2*H=A^2+B^2 → IsSquare H →
      (ZMod.castHom (by decide : 8 ∣ 16) (ZMod 8)) A=(ZMod.castHom (by decide : 8 ∣ 16) (ZMod 8)) B ∨
      (ZMod.castHom (by decide : 8 ∣ 16) (ZMod 8)) A= -(ZMod.castHom (by decide : 8 ∣ 16) (ZMod 8)) B := by decide
  have hsign := hfinite_sign _ _ _ ha4 hb4 hHr (hHsq.map (PadicInt.toZModPow 4))
  have hcast (t : ℤ_[2]) : (ZMod.castHom (by decide : 8 ∣ 16) (ZMod 8)) (PadicInt.toZModPow 4 t)=
      PadicInt.toZModPow 3 t := by
    simpa only [ZMod.castHom_apply] using PadicInt.cast_toZModPow (p:=2) 3 4 (by decide) t
  rw [hcast,hcast] at hsign
  simpa only [phiEight_formula,a,b] using hsign

#print axioms actual_depth_three_square_sign
end
end FourCorner.Cs15569Completion
