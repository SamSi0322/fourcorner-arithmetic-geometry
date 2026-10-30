import HpOddSourceOpen

namespace FourCorner.HpFamilyResidue
open HpInfiniteArithmetic HpFamilyDyadicValuation
noncomputable section
variable {q : ℕ} [Fact q.Prime]

/-- Every rational root whose square is an integral radicand is itself
integral; the residue equations are therefore taken on actual source roots. -/
theorem integral_square_root (x : ℚ_[q]) (A : ℤ_[q]) (h : x^2=(A : ℚ_[q])) :
    ∃X : ℤ_[q],(X : ℚ_[q])=x := by
  have hn : ‖x‖^2≤1 := by rw [← norm_pow,h];exact A.property
  have hx : ‖x‖≤1 := by nlinarith [norm_nonneg x]
  exact ⟨⟨x,hx⟩,rfl⟩

/-- The two displayed rational conics survive in the actual residue field
at every integral family parameter. -/
theorem conic_squares (j : ℕ) (P : ℤ_[q]) (hP : (P : ℚ_[q])=(p j : ℚ_[q])) :
    IsSquare (2*(PadicInt.toZMod P+1)) ∧ IsSquare (3-PadicInt.toZMod P) := by
  have hr : (r j : ℚ_[q])^2=((2*(P+1) : ℤ_[q]) : ℚ_[q]) := by
    simp only [PadicInt.coe_mul,PadicInt.coe_add,PadicInt.coe_one,hP]
    have hh : ((r j)^2 : ℚ) =2*(p j+1) := r_square j
    change (r j : ℚ_[q])^2=2*((p j : ℚ_[q])+1)
    exact_mod_cast hh
  have hs : (s j : ℚ_[q])^2=((3-P : ℤ_[q]) : ℚ_[q]) := by
    simp only [PadicInt.coe_sub,hP]
    change (s j : ℚ_[q])^2=(3 : ℚ_[q])-(p j : ℚ_[q])
    have hh : (s j)^2=3-p j := by unfold p;ring
    exact_mod_cast hh
  obtain ⟨R,hR⟩ := integral_square_root _ _ hr
  obtain ⟨S,hS⟩ := integral_square_root _ _ hs
  have hR2 : R^2=2*(P+1) := by
    apply Subtype.ext
    simpa only [PadicInt.coe_pow,hR] using hr
  have hS2 : S^2=3-P := by
    apply Subtype.ext
    simpa only [PadicInt.coe_pow,hS] using hs
  constructor
  · have hh := congrArg PadicInt.toZMod hR2
    simp only [map_pow,map_mul,map_add,map_one,map_ofNat] at hh
    exact ⟨PadicInt.toZMod R,by simpa only [pow_two] using hh.symm⟩
  · have hh := congrArg PadicInt.toZMod hS2
    simp only [map_pow,map_sub,map_ofNat] at hh
    exact ⟨PadicInt.toZMod S,by simpa only [pow_two] using hh.symm⟩

/-- An integral presentation of the EXACT rational family is available
when the displayed conic denominator has nonzero reduction. -/
theorem integral_presentation (j : ℕ)
    (hD : ((NN j : ZMod q)^2+2*(MM j : ZMod q)^2) ≠ 0) :
    ∃P : ℤ_[q],(P : ℚ_[q])=(p j : ℚ_[q]) ∧
      PadicInt.toZMod P=3-(2*((NN j : ZMod q)^2-2*(MM j : ZMod q)^2)/
        ((NN j : ZMod q)^2+2*(MM j : ZMod q)^2))^2 := by
  let n : ℤ_[q] := NN j
  let m : ℤ_[q] := MM j
  let d : ℤ_[q] := n^2+2*m^2
  have hdres : PadicInt.toZMod d ≠ 0 := by
    simpa only [d,n,m,map_add,map_pow,map_mul,map_ofNat,map_natCast] using hD
  have hdunit := HpGoodFiniteLift.norm_eq_one_of_residue d hdres
  let di : ℤ_[q] := ⟨(d : ℚ_[q])⁻¹,by rw [norm_inv,hdunit];norm_num⟩
  let s0 : ℤ_[q] := 2*(n^2-2*m^2)*di
  let P : ℤ_[q] := 3-s0^2
  have hd0 : (d : ℚ_[q]) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hdunit]
    norm_num
  have hdid : d*di=1 := by apply Subtype.ext;exact mul_inv_cancel₀ hd0
  have hdires : PadicInt.toZMod di=(PadicInt.toZMod d)⁻¹ := by
    have hh := congrArg PadicInt.toZMod hdid
    rw [map_mul,map_one] at hh
    apply mul_left_cancel₀ hdres
    rwa [mul_inv_cancel₀ hdres]
  have hn : (n : ℚ_[q])=(N j : ℚ_[q]) := by dsimp [n];rw [← N_cast];push_cast;rfl
  have hm : (m : ℚ_[q])=(M j : ℚ_[q]) := by dsimp [m];rw [← M_cast];push_cast;rfl
  have hd : (d : ℚ_[q])=(D j : ℚ_[q]) := by
    change (n : ℚ_[q])^2+2*(m : ℚ_[q])^2=(D j : ℚ_[q])
    rw [hn,hm]
    simp only [D,Rat.cast_add,Rat.cast_pow,Rat.cast_mul,Rat.cast_ofNat]
  have hs : (s0 : ℚ_[q])=(s j : ℚ_[q]) := by
    change 2*((n : ℚ_[q])^2-2*(m : ℚ_[q])^2)*(d : ℚ_[q])⁻¹=(s j : ℚ_[q])
    rw [hn,hm,hd]
    simp only [s,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_pow,Rat.cast_ofNat,div_eq_mul_inv,Rat.cast_inv]
  refine ⟨P,?_,?_⟩
  · change (3 : ℚ_[q])-(s0 : ℚ_[q])^2=(p j : ℚ_[q])
    rw [hs]
    simp only [p,Rat.cast_sub,Rat.cast_pow,Rat.cast_ofNat]
  · dsimp [P,s0]
    simp only [map_sub,map_pow,map_mul,map_ofNat,hdires,d,n,m,map_add,map_natCast]
    rfl

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

theorem residue_seven (j : ℕ) (P : ℤ_[7]) (hP : (P : ℚ_[7])=(p j : ℚ_[7])) : PadicInt.toZMod P=1 := by
  have hn : (NN j : ZMod 7)=3 := by
    rw [NN,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_ofNat,show (154 : ZMod 7)=0 from by decide]
    ring
  have hm : (MM j : ZMod 7)=5 := by rw [MM,Nat.cast_add,hn];decide
  obtain ⟨P',hP',hres⟩ := integral_presentation (q:=7) j (by rw [hn,hm];decide)
  have he : P=P' := Subtype.ext (hP.trans hP'.symm)
  rw [he,hres,hn,hm]
  have hd : (3 : ZMod 7)^2+2*5^2=3 := by decide
  have hi : (3 : ZMod 7)⁻¹=5 := by
    apply mul_left_cancel₀ (by decide : (3 : ZMod 7) ≠ 0)
    rw [mul_inv_cancel₀ (by decide : (3 : ZMod 7) ≠ 0)]
    decide
  rw [hd,div_eq_mul_inv,hi]
  decide

 theorem residue_eleven (j : ℕ) (P : ℤ_[11]) (hP : (P : ℚ_[11])=(p j : ℚ_[11])) : PadicInt.toZMod P=9 := by
  have hn : (NN j : ZMod 11)=3 := by
    rw [NN,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_ofNat,show (154 : ZMod 11)=0 from by decide]
    ring
  have hm : (MM j : ZMod 11)=5 := by rw [MM,Nat.cast_add,hn];decide
  obtain ⟨P',hP',hres⟩ := integral_presentation (q:=11) j (by rw [hn,hm];decide)
  have he : P=P' := Subtype.ext (hP.trans hP'.symm)
  rw [he,hres,hn,hm]
  have hd : (3 : ZMod 11)^2+2*5^2=4 := by decide
  have hi : (4 : ZMod 11)⁻¹=3 := by
    apply mul_left_cancel₀ (by decide : (4 : ZMod 11) ≠ 0)
    rw [mul_inv_cancel₀ (by decide : (4 : ZMod 11) ≠ 0)]
    decide
  rw [hd,div_eq_mul_inv,hi]
  decide

#print axioms conic_squares
#print axioms integral_presentation
#print axioms residue_seven
#print axioms residue_eleven
end
end FourCorner.HpFamilyResidue
