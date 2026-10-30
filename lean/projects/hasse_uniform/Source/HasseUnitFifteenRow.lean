import HasseUnitFifteenSign
import HasseWR

namespace FourCorner.HasseUnitFifteenRow

open HasseDyadicSymbol HasseDyadicAlgebra HasseConstantDyadic HasseDyadicUnitFifteenModel
open HasseUnitFifteenFactor HasseUnitFifteenNormalization HasseUnitFifteenSign
open HasseRationalSource HasseAnchorChoice HasseTangentGlobal HasseObstructionArithmetic

noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem unitFifteen_square_depth (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p) (h : UnitFifteen p) :
    IsSquare (((p : ℚ_[2])+1)/2) ∧ 5≤((p : ℚ_[2])+1).valuation := by
  have hv := unitFifteen_val_zero p h
  rcases HasseNorms.dyadic_conclusion p hp hL with hd | hd | hd | hd
  · rw [hv] at hd;omega
  · rw [hv] at hd;omega
  · obtain ⟨u,hu,hr,_⟩ := hd
    exact False.elim (unit_branches_disjoint p ⟨⟨u,hu,hr⟩,h⟩)
  · exact ⟨hd.choose_spec.2.2.1,hd.choose_spec.2.2.2.2⟩

/-- Complete unit-fifteen dyadic evaluation of the SAME original source
tangent coefficient. Every U orientation is included through a proved
polar-product identity; no Brauer evaluation transfer is assumed. -/
theorem tangentSign_unitFifteen (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) (h : UnitFifteen p) :
    tangentSign p hp P D 2=HasseWR.wSign p hp P D 2*
      (-1 : ℤ)^(if padicValRat 2 (p+1)=5 then 1 else 0) := by
  obtain ⟨hroot,hdepth⟩ := unitFifteen_square_depth p hp hL h
  obtain ⟨s,x,y,z,hs,hx,hy,hz,hsv,hxv,hyv,hzv,hpeq,heqx,heqy,hU,hW,hT⟩ :=
    HasseUnitFifteenNormalization.source_normal_form p hp P D hroot hdepth
  have hp0 : (p : ℚ_[2]) ≠ 0 := by exact_mod_cast (show p ≠ 0 by linarith)
  have hZ0 : (P.Z : ℚ_[2]) ≠ 0 := by exact_mod_cast (coordinates_ne_zero p hp P).1
  have hC0 : (firstCoefficient p : ℚ_[2]) ≠ 0 := by exact_mod_cast (ne_of_lt (firstCoefficient_negative p hp))
  have hF0 : (secondCoefficient p P D : ℚ_[2]) ≠ 0 := by exact_mod_cast (ne_of_lt D.coefficient_negative)
  have hb0 : (p : ℚ_[2])+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  have hc : (firstCoefficient p : ℚ_[2])=2*(1-s^2) := by
    simp only [firstCoefficient,Rat.cast_neg,Rat.cast_sub,Rat.cast_one]
    rw [hpeq]
    ring
  have hb : (p : ℚ_[2])+1=2*s^2 := by rw [hpeq];ring
  have hAsq := square_one_sub_s s hs hsv
  have hcb : dyadicSign (firstCoefficient p : ℚ_[2]) ((p : ℚ_[2])+1) hC0 hb0=1 := by
    have hratio : IsSquare ((firstCoefficient p : ℚ_[2])/2) := by
      have he : (firstCoefficient p : ℚ_[2])/2=1-s^2 := by rw [hc];ring
      rwa [he]
    have hleft := dyadicSign_eq_of_square_ratio (firstCoefficient p : ℚ_[2]) 2 ((p : ℚ_[2])+1)
      hC0 (by norm_num) hb0 hratio
    have hh := dyadicSign_mul_sq_right (2 : ℚ_[2]) 2 s (by norm_num) (by norm_num) hs
    rw [dyadicSign_two_two] at hh
    have hright : dyadicSign 2 ((p : ℚ_[2])+1) (by norm_num) hb0=1 := by simpa only [← hb] using hh
    exact hleft.trans hright
  have hRaw : (secondCoefficient p P D : ℚ_[2])=
      coefficient (p : ℚ_[2]) (P.Z : ℚ_[2]) (P.U : ℚ_[2]) (D.w : ℚ_[2]) (P.T : ℚ_[2]) := by
    dsimp [secondCoefficient,secondPolar,anchorU,anchorT,anchorZ,coefficient]
    push_cast
    ring
  have hRawPos : (secondCoefficient p P D : ℚ_[2])=
      coefficient (p : ℚ_[2]) (P.Z : ℚ_[2]) (s*x*(P.Z : ℚ_[2]))
        (2*s*y*(P.Z : ℚ_[2])) (2*s*z*(P.Z : ℚ_[2])) := by rw [hRaw,hU,hW,hT]
  have hratio : ((D.w/P.Z : ℚ) : ℚ_[2])=2*s*y := by
    push_cast
    rw [hW]
    field_simp
  have hwSign : HasseWR.wSign p hp P D 2=
      dyadicSign 2 (2*s*y) (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hs) hy) := by
    have hh := rationalSign_eq_dyadicSign 2 (D.w/P.Z) (by norm_num) (HasseWR.ratio_ne_zero p hp P D)
    simpa only [HasseWR.wSign,HasseWR.ratio,Rat.cast_ofNat,hratio] using hh
  have hmodel : tangentSign p hp P D 2=HasseWR.wSign p hp P D 2*
      (if s.valuation=2 then -1 else 1) := by
    obtain ⟨x',hchoice,hx',hxv',ho⟩ := oriented_sign_exists x y hx hy hxv
    rcases hchoice with he | he
    · subst x'
      obtain ⟨hc',hF',hSign⟩ := oriented_coefficient_sign (p : ℚ_[2]) (P.Z : ℚ_[2]) s x y z
        hp0 hZ0 hs hx hy hz hsv hxv hyv hzv hpeq heqx heqy ho
      have hSign' : dyadicSign (firstCoefficient p : ℚ_[2]) (secondCoefficient p P D : ℚ_[2]) hC0 hF0=
          HasseWR.wSign p hp P D 2*(if s.valuation=2 then -1 else 1) := by
        simpa only [← hc,← hRawPos,← hwSign] using hSign
      exact (tangentSign_eq_dyadicSign p hp P D).trans hSign'
    · subst x'
      have hUNeg : -(P.U : ℚ_[2])=s*(-x)*(P.Z : ℚ_[2]) := by rw [hU];ring
      obtain ⟨hFflip,hFlip⟩ := source_coefficient_flip p hp P D hcb
      have hFlipModel : coefficient (p : ℚ_[2]) (P.Z : ℚ_[2]) (-(P.U : ℚ_[2])) (D.w : ℚ_[2]) (P.T : ℚ_[2])=
          coefficient (p : ℚ_[2]) (P.Z : ℚ_[2]) (s*(-x)*(P.Z : ℚ_[2]))
            (2*s*y*(P.Z : ℚ_[2])) (2*s*z*(P.Z : ℚ_[2])) := by rw [hUNeg,hW,hT]
      obtain ⟨hc',hF',hSign⟩ := oriented_coefficient_sign (p : ℚ_[2]) (P.Z : ℚ_[2]) s (-x) y z
        hp0 hZ0 hs (neg_ne_zero.mpr hx) hy hz hsv (by rw [commonRoot_val_neg,hxv]) hyv hzv hpeq
        (by simpa only [neg_sq] using heqx) heqy ho
      have hSign' : dyadicSign (firstCoefficient p : ℚ_[2])
          (coefficient (p : ℚ_[2]) (P.Z : ℚ_[2]) (-(P.U : ℚ_[2])) (D.w : ℚ_[2]) (P.T : ℚ_[2])) hC0 hFflip=
          HasseWR.wSign p hp P D 2*(if s.valuation=2 then -1 else 1) := by
        simpa only [← hc,← hFlipModel,← hwSign] using hSign
      exact (tangentSign_eq_dyadicSign p hp P D).trans (hFlip.trans hSign')
  have hvb : padicValRat 2 (p+1)=1+2*s.valuation := by
    have he : ((p+1 : ℚ) : ℚ_[2])=2*s^2 := by push_cast;exact hb
    rw [← Padic.valuation_ratCast,he,Padic.valuation_mul (by norm_num) (pow_ne_zero _ hs),
      Padic.valuation_pow,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
    norm_num
  have hbit : (if s.valuation=2 then (-1 : ℤ) else 1)=
      (-1 : ℤ)^(if padicValRat 2 (p+1)=5 then 1 else 0) := by
    by_cases hv : s.valuation=2
    · have hh : padicValRat 2 (p+1)=5 := by omega
      simp [hv,hh]
    · have hh : padicValRat 2 (p+1) ≠ 5 := by omega
      simp [hv,hh]
  exact hmodel.trans (congrArg (HasseWR.wSign p hp P D 2*·) hbit)

#print axioms tangentSign_unitFifteen

end
end FourCorner.HasseUnitFifteenRow
