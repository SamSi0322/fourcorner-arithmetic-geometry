import Cs15569DyadicResidues

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace FourCorner.Cs15569Completion
noncomputable section

/-- Actual global first-slot support forces an even valuation. -/
theorem first_supported_even {q : ℚ} (hs : FirstSupportedClass q) :
    Even (padicValRat 2 q) := by
  obtain ⟨d,hd,u,hu,he⟩ := hs
  have hd0 : d ≠ 0 := by rcases hd with h | h | h | h <;> rw [h] <;> norm_num
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  rw [he,padicValRat.mul hdq (pow_ne_zero _ hu.ne'),padicValRat.pow,first_class_val_zero hd]
  refine ⟨padicValRat 2 u,?_⟩
  ring

/-- Every negative abscissa valuation on the actual rational curve is
already in the paper's H-neighborhood. -/
theorem negative_valuation_deep {x y : ℚ} (h : y^2=x*(x-15569)*(x+15569))
    (hv : padicValRat 2 x<0) : padicValRat 2 x≤ -4 := by
  have hx : x ≠ 0 := by intro hz; simp [hz] at hv
  obtain ⟨k,hk⟩ := first_supported_even (first_support hx h)
  have hn := no_minus_two h
  omega

/-- A globally supported unit has integral reduction +1 or -1 modulo8. -/
theorem first_class_unit_mod8 {q : ℚ} (hs : FirstSupportedClass q)
    (hv : padicValRat 2 q=0) :
    ∃ X : ℤ_[2], (X : ℚ_[2])=(q : ℚ_[2]) ∧
      (PadicInt.toZModPow 3 X=1 ∨ PadicInt.toZModPow 3 X= -1) := by
  have hq : q ≠ 0 := by
    obtain ⟨d,hd,u,hu,he⟩ := hs
    rw [he]
    have hdq : (d : ℚ) ≠ 0 := by
      rcases hd with h | h | h | h <;> rw [h] <;> norm_num
    exact mul_ne_zero hdq (pow_ne_zero _ hu.ne')
  have hs' : FirstSupportedClass (q/4) := by
    obtain ⟨d,hd,u,hu,he⟩ := hs
    refine ⟨d,hd,u/2,by positivity,?_⟩
    rw [he]
    ring
  have hv' : padicValRat 2 (q/4)= -2 := by
    have h4 : padicValRat 2 (4 : ℚ)=2 := by
      rw [show (4 : ℚ)=2^2 by norm_num,padicValRat.pow]
      have htwo : padicValRat 2 (2 : ℚ)=1 := by
        simpa only [Nat.cast_ofNat] using (padicValRat.self (p:=2) (by norm_num))
      rw [htwo]
      norm_num
    rw [padicValRat.div hq (by norm_num),hv,h4]
    norm_num
  obtain ⟨X,hX,hr⟩ := first_class_at_minus_two hs' hv'
  refine ⟨X,?_,hr⟩
  rw [hX]
  push_cast
  ring

private theorem n_cast_dyadic : ((15569 : ℤ_[2]) : ℚ_[2])=(15569 : ℚ_[2]) := by
  change (((15569 : ℕ) : ℤ_[2]) : ℚ_[2])=15569
  rw [PadicInt.coe_natCast]
  norm_num

private theorem n_residue_dyadic : PadicInt.toZModPow 3 (15569 : ℤ_[2])=(1 : ZMod 8) := by
  change PadicInt.toZModPow 3 ((15569 : ℕ) : ℤ_[2])=1
  rw [map_natCast]
  decide

/-- Actual integral residue zero implies the corresponding rational point
has offset valuation at least three. -/
private theorem offset_depth_from_zero {X : ℤ_[2]} {r : ℚ}
    (hr : (X : ℚ_[2])=(r : ℚ_[2])) (hr0 : r ≠ 0)
    (hzero : PadicInt.toZModPow 3 X=0) : 3≤padicValRat 2 r := by
  have hX0 : X ≠ 0 := by
    intro hz
    have hh : (r : ℚ_[2])=0 := by rw [←hr,hz]; rfl
    exact hr0 (by exact_mod_cast hh)
  have hnorm := (dyadic_residue_zero_iff_norm_le X 3).mp hzero
  have hv := (PadicInt.norm_le_pow_iff_le_valuation X hX0 3).mp hnorm
  have hv' : (3 : ℤ)≤(X : ℚ_[2]).valuation := by
    rw [PadicInt.valuation_coe]
    exact_mod_cast hv
  rw [hr,Padic.valuation_ratCast] at hv'
  exact hv'

/-- Exhaustive unit case: an ordinary rational curve point with v2(x)=0
is within depth at least three of one of the actual roots +n,-n. -/
theorem unit_offset_deep {x y : ℚ}
    (h : y^2=x*(x-15569)*(x+15569)) (hx : x ≠ 0)
    (hm : x-15569 ≠ 0) (hp : x+15569 ≠ 0) (hv : padicValRat 2 x=0) :
    3≤padicValRat 2 (x-15569) ∨ 3≤padicValRat 2 (x+15569) := by
  obtain ⟨X,hX,hr⟩ := first_class_unit_mod8 (first_support hx h) hv
  rcases hr with hr | hr
  · left
    have heq : ((X-15569 : ℤ_[2]) : ℚ_[2])=((x-15569 : ℚ) : ℚ_[2]) := by
      rw [PadicInt.coe_sub,hX,n_cast_dyadic]
      push_cast
      rfl
    apply offset_depth_from_zero heq hm
    rw [map_sub,hr,n_residue_dyadic]
    ring
  · right
    have heq : ((X+15569 : ℤ_[2]) : ℚ_[2])=((x+15569 : ℚ) : ℚ_[2]) := by
      rw [PadicInt.coe_add,hX,n_cast_dyadic]
      push_cast
      rfl
    apply offset_depth_from_zero heq hp
    rw [map_add,hr,n_residue_dyadic]
    ring

#print axioms negative_valuation_deep
#print axioms first_class_unit_mod8
#print axioms unit_offset_deep
end
end FourCorner.Cs15569Completion
