import HasseConstantOdd
import HasseDyadicNonunit

namespace FourCorner.HasseConstantDyadic

open HasseDyadicSymbol HasseDyadicNonunit HasseObstructionArithmetic HasseConstantCorrection
open HasseRationalSource HasseAnchorChoice HasseTangentGlobal

theorem unitOne_val_zero (p : ℚ) (h : UnitOne p) : (p : ℚ_[2]).valuation=0 := by
  obtain ⟨u,hu,hr⟩ := h
  have hh := HasseDyadicBranches.val_zero_of_residue_one_or_fifteen u (Or.inl hr)
  rwa [hu] at hh

theorem unitFifteen_val_zero (p : ℚ) (h : UnitFifteen p) : (p : ℚ_[2]).valuation=0 := by
  obtain ⟨u,hu,hr⟩ := h
  have hh := HasseDyadicBranches.val_zero_of_residue_one_or_fifteen u (Or.inr hr)
  rwa [hu] at hh

theorem unitOne_half_square (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p) (h : UnitOne p) :
    IsSquare (((p : ℚ_[2])-1)/2) := by
  have hv := unitOne_val_zero p h
  rcases HasseNorms.dyadic_conclusion p hp hL with hd | hd | hd | hd
  · rw [hv] at hd
    omega
  · rw [hv] at hd
    omega
  · obtain ⟨u,hu,hr,hsq,hodd,hge⟩ := hd
    exact hsq
  · obtain ⟨u,hu,hr,_⟩ := hd
    exact False.elim (unit_branches_disjoint p ⟨h,u,hu,hr⟩)

theorem unitFifteen_b_depth (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p) (h : UnitFifteen p) :
    5≤((p : ℚ_[2])+1).valuation := by
  have hv := unitFifteen_val_zero p h
  rcases HasseNorms.dyadic_conclusion p hp hL with hd | hd | hd | hd
  · rw [hv] at hd
    omega
  · rw [hv] at hd
    omega
  · obtain ⟨u,hu,hr,_⟩ := hd
    exact False.elim (unit_branches_disjoint p ⟨⟨u,hu,hr⟩,h⟩)
  · obtain ⟨u,hu,hr,hsq,hodd,hge⟩ := hd
    exact hge

theorem dyadicSign_eq_of_square_ratio (x c y : ℚ_[2]) (hx : x ≠ 0) (hc : c ≠ 0) (hy : y ≠ 0)
    (hsq : IsSquare (x/c)) : dyadicSign x y hx hy=dyadicSign c y hc hy := by
  obtain ⟨s,hs⟩ := hsq
  have he : x=c*s^2 := by
    have he' : x/c=s^2 := by simpa only [pow_two] using hs
    exact (div_eq_iff hc).mp he' |>.trans (mul_comm _ _)
  have hs0 : s ≠ 0 := by intro hz; apply hx; simp [he,hz]
  have hh := dyadicSign_mul_sq_left c y s hc hy hs0
  simpa only [← he] using hh

theorem constantSign_unitOne (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p) (h : UnitOne p) :
    constantSign p hp 2= -1 := by
  rw [constantSign,rationalSign_eq_dyadicSign]
  have hs := unitOne_half_square p hp hL h
  have hratio : IsSquare ((firstCoefficient p : ℚ_[2])/(-2)) := by
    convert hs using 1 <;> simp only [firstCoefficient,Rat.cast_neg,Rat.cast_sub,Rat.cast_one] <;> ring
  have hx : (firstCoefficient p : ℚ_[2]) ≠ 0 := by exact_mod_cast (ne_of_lt (firstCoefficient_negative p hp))
  have hl : dyadicSign (firstCoefficient p : ℚ_[2]) (-2) hx (by norm_num)= -1 :=
    (dyadicSign_eq_of_square_ratio _ (-2) (-2) hx (by norm_num) (by norm_num) hratio).trans
      dyadicSign_negTwo_negTwo
  simpa only [Rat.cast_neg,Rat.cast_ofNat] using hl

theorem constantSign_unitFifteen (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p) (h : UnitFifteen p) :
    constantSign p hp 2=1 := by
  rw [constantSign,rationalSign_eq_dyadicSign]
  have hb0 : (p : ℚ_[2])+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  have hdep := unitFifteen_b_depth p hp hL h
  have hv : 3≤(-(((p : ℚ_[2])+1)/2)).valuation := by
    rw [commonRoot_val_neg,commonRoot_val_div hb0 (by norm_num),
      show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
    omega
  have hs := HasseUnitBranches.square_one_add_of_val_ge_three (-(((p : ℚ_[2])+1)/2)) hv
  have hratio : IsSquare ((firstCoefficient p : ℚ_[2])/2) := by
    convert hs using 1 <;> simp only [firstCoefficient,Rat.cast_neg,Rat.cast_sub,Rat.cast_one] <;> ring
  have hx : (firstCoefficient p : ℚ_[2]) ≠ 0 := by exact_mod_cast (ne_of_lt (firstCoefficient_negative p hp))
  have hl : dyadicSign (firstCoefficient p : ℚ_[2]) (-2) hx (by norm_num)=1 :=
    (dyadicSign_eq_of_square_ratio _ 2 (-2) hx (by norm_num) (by norm_num) hratio).trans
      dyadicSign_two_negTwo
  simpa only [Rat.cast_neg,Rat.cast_ofNat] using hl

theorem nonunit_firstCoefficient_square (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (hv : padicValRat 2 p ≠ 0) : IsSquare (firstCoefficient p : ℚ_[2]) := by
  rcases HasseNorms.dyadic_conclusion p hp hL with hd | hd | hd | hd
  · exact firstCoefficient_square_positive p (by linarith) (by omega)
  · exact firstCoefficient_square_negative p hp P hd.1
  · obtain ⟨u,hu,hr,_⟩ := hd
    have hh := unitOne_val_zero p ⟨u,hu,hr⟩
    rw [Padic.valuation_ratCast] at hh
    exact False.elim (hv hh)
  · obtain ⟨u,hu,hr,_⟩ := hd
    have hh := unitFifteen_val_zero p ⟨u,hu,hr⟩
    rw [Padic.valuation_ratCast] at hh
    exact False.elim (hv hh)

theorem constantSign_nonunit (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (hv : padicValRat 2 p ≠ 0) : constantSign p hp 2=1 := by
  rw [constantSign,rationalSign_eq_dyadicSign]
  apply dyadicSign_one_of_left_square
  exact nonunit_firstCoefficient_square p hp hL P hv

theorem correctedSign_nonunit (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hv : padicValRat 2 p ≠ 0) :
    correctedSign p hp P D 2=1 := by
  have htan : tangentSign p hp P D 2=1 := by
    rw [tangentSign_eq_dyadicSign]
    apply dyadicSign_one_of_left_square
    exact nonunit_firstCoefficient_square p hp hL P hv
  rw [correctedSign,htan,constantSign_nonunit p hp hL P hv,one_mul]

#print axioms constantSign_unitOne
#print axioms constantSign_unitFifteen
#print axioms constantSign_nonunit
#print axioms correctedSign_nonunit

end FourCorner.HasseConstantDyadic
