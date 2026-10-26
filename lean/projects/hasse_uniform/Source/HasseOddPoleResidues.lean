import HasseOddPoleCoordinates
namespace FourCorner.HasseOddPoleResidues
open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HassePoleParameters HassePositiveBInert HasseRationalNormalization HasseOddPoleCoordinates

variable {q : ℕ} [Fact q.Prime]

theorem integral_residue_one_of_sub_one_positive (x : ℚ_[q]) (hv : x.valuation=0)
    (hd : 0<(x-1).valuation) :
    PadicInt.toZMod (integralOfVal x (by omega))=1 := by
  let xi := integralOfVal x (by omega : 0≤x.valuation)
  have he : xi-1=integralOfVal (x-1) (by omega : 0≤(x-1).valuation) := rfl
  have hh := integral_residue_zero_of_positive (x-1) hd
  rw [← he,map_sub,map_one] at hh
  linear_combination hh

/-- Literal original-source normalized residue coordinates at an odd pole. -/
theorem residue_coordinates_at_odd_pole (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hT : P.T=1)
    (hv : padicValRat Q.val p<0) (hodd : Odd (padicValRat Q.val p)) :
    ∃ u w z : ℤ_[Q.val], (u : ℚ_[Q.val])=(P.U : ℚ_[Q.val]) ∧
      (w : ℚ_[Q.val])=(D.w : ℚ_[Q.val]) ∧ (z : ℚ_[Q.val])=(P.Z : ℚ_[Q.val]) ∧
      (PadicInt.toZMod u)^2=1 ∧ (PadicInt.toZMod w)^2=2 ∧ PadicInt.toZMod z=0 := by
  have hp0 : p ≠ 0 := by linarith
  have ha0 : p-1 ≠ 0 := by linarith
  have hb0 : p+1 ≠ 0 := by linarith
  have hc := unit_coordinates_at_odd_pole Q p hp P D hT hv hodd
  have hzv : 0<(P.Z : ℚ_[Q.val]).valuation := by rw [Padic.valuation_ratCast]; exact hc.1
  have huv : (P.U : ℚ_[Q.val]).valuation=0 := by rw [Padic.valuation_ratCast]; exact hc.2.1
  have hwv : (D.w : ℚ_[Q.val]).valuation=0 := by rw [Padic.valuation_ratCast]; exact hc.2.2
  obtain ⟨hZ,hU,hV,hW,hTT⟩ := coordinates_ne_zero p hp P
  have haq : ((p-1 : ℚ) : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast ha0
  have hpq : (p : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hp0
  have hbq : ((p+1 : ℚ) : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hb0
  have hzq : (P.Z : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hZ
  let u := integralOfVal (P.U : ℚ_[Q.val]) (by omega : 0≤(P.U : ℚ_[Q.val]).valuation)
  let w := integralOfVal (D.w : ℚ_[Q.val]) (by omega : 0≤(D.w : ℚ_[Q.val]).valuation)
  let z := integralOfVal (P.Z : ℚ_[Q.val]) (by omega : 0≤(P.Z : ℚ_[Q.val]).valuation)
  let rp : ℚ_[Q.val] := ((p/(p-1) : ℚ) : ℚ_[Q.val])
  let rb : ℚ_[Q.val] := (((p+1)/(p-1) : ℚ) : ℚ_[Q.val])
  have hrpv : rp.valuation=0 := by
    dsimp [rp]
    rw [Rat.cast_div,commonRoot_val_div hpq haq,pole_a_valuation Q p hp hv]
    omega
  have hrbv : rb.valuation=0 := by
    dsimp [rb]
    rw [Rat.cast_div,commonRoot_val_div hbq haq,pole_b_valuation Q p hp hv,pole_a_valuation Q p hp hv]
    omega
  have hrpd : 0<(rp-1).valuation := by
    have he : rp-1=1/(((p-1 : ℚ) : ℚ_[Q.val])) := by
      dsimp [rp]
      exact_mod_cast (show p/(p-1)-1=1/(p-1) from by field_simp; ring)
    rw [he,commonRoot_val_div one_ne_zero haq,Padic.valuation_one,pole_a_valuation Q p hp hv,Padic.valuation_ratCast]
    omega
  have hrbd : 0<(rb-1).valuation := by
    have he : rb-1=2/(((p-1 : ℚ) : ℚ_[Q.val])) := by
      dsimp [rb]
      exact_mod_cast (show (p+1)/(p-1)-1=2/(p-1) from by field_simp; ring)
    rw [he,commonRoot_val_div (by norm_num) haq,commonRoot_val_two Q.property.2,
      pole_a_valuation Q p hp hv,Padic.valuation_ratCast]
    omega
  let rpi := integralOfVal rp (by omega : 0≤rp.valuation)
  let rbi := integralOfVal rb (by omega : 0≤rb.valuation)
  have hrpi : PadicInt.toZMod rpi=1 := integral_residue_one_of_sub_one_positive rp hrpv hrpd
  have hrbi : PadicInt.toZMod rbi=1 := integral_residue_one_of_sub_one_positive rb hrbv hrbd
  let bz2 : ℚ_[Q.val] := (((p+1)*P.Z^2 : ℚ) : ℚ_[Q.val])
  have hbzv : 0<bz2.valuation := by
    dsimp [bz2]
    rw [Padic.valuation_ratCast,padicValRat.mul hb0 (pow_ne_zero _ hZ),padicValRat.pow]
    have hb := pole_b_valuation Q p hp hv
    rw [Padic.valuation_ratCast,Padic.valuation_ratCast] at hb
    rw [hb]
    exact z_depth_at_odd_pole Q p hp P D hT hv hodd
  let bzi := integralOfVal bz2 (by omega : 0≤bz2.valuation)
  have hbzi : PadicInt.toZMod bzi=0 := integral_residue_zero_of_positive bz2 hbzv
  have hzi : PadicInt.toZMod z=0 := integral_residue_zero_of_positive _ hzv
  have hU : u^2=rpi*(1-bzi) := by
    apply Subtype.ext
    change (P.U : ℚ_[Q.val])^2=rp*(1-bz2)
    have he : P.U^2=(p/(p-1))*(1-(p+1)*P.Z^2) := by
      have he3 := P.equations.2.2
      rw [hT] at he3
      field_simp
      linear_combination -he3
    dsimp [rp,bz2]
    exact_mod_cast he
  have hW : w^2=2*rbi*(1-2*z^2) := by
    apply Subtype.ext
    change (D.w : ℚ_[Q.val])^2=2*rb*(1-2*(P.Z : ℚ_[Q.val])^2)
    have he : D.w^2=2*((p+1)/(p-1))*(1-2*P.Z^2) := by
      have he3 := D.omission.2
      rw [hT] at he3
      field_simp
      linear_combination he3
    dsimp [rb]
    exact_mod_cast he
  refine ⟨u,w,z,rfl,rfl,rfl,?_,?_,hzi⟩
  · have hh := congrArg PadicInt.toZMod hU
    simpa only [map_pow,map_mul,map_sub,map_one,hrpi,hbzi,sub_zero,one_mul] using hh
  · have hh := congrArg PadicInt.toZMod hW
    simpa only [map_pow,map_mul,map_sub,map_one,map_ofNat,hrbi,hzi,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero,mul_one] using hh

#print axioms integral_residue_one_of_sub_one_positive
#print axioms residue_coordinates_at_odd_pole
end FourCorner.HasseOddPoleResidues
