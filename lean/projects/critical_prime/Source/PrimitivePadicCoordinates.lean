import PadicUnitNormalization
import Mathlib.Data.Int.GCD

noncomputable section
namespace FourCorner.PrimitivePadicCoordinates
variable {p : ℕ} [Fact p.Prime]

/-- Joint primitivity is used on the original three integer coordinates. -/
theorem coordinate_residues_nonzero (X Y L : ℤ)
    (hprim : Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs=1)
    (hL : (L:ZMod p)=0) (hnorm : (X:ZMod p)^2+(Y:ZMod p)^2=0) :
    (X:ZMod p)≠0 ∧ (Y:ZMod p)≠0 := by
  have hboth (hx : (X:ZMod p)=0) (hy : (Y:ZMod p)=0) : False := by
    have hdx : p∣X.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd X p).mp hx)
    have hdy : p∣Y.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd Y p).mp hy)
    have hdl : p∣L.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd L p).mp hL)
    have hd:=Nat.dvd_gcd (Nat.dvd_gcd hdx hdy) hdl
    rw [hprim] at hd
    exact (Fact.out : p.Prime).not_dvd_one hd
  constructor
  · intro hx
    have hy : (Y:ZMod p)=0 := sq_eq_zero_iff.mp (by simpa only [hx,zero_pow (by decide : 2≠0),zero_add] using hnorm)
    exact hboth hx hy
  · intro hy
    have hx : (X:ZMod p)=0 := sq_eq_zero_iff.mp (by simpa only [hy,zero_pow (by decide : 2≠0),add_zero] using hnorm)
    exact hboth hx hy

/-- Positive valuation of an ACTUAL Qp origin radius reduces the original
integer norm to zero; no integer radius is introduced. -/
theorem norm_residue_zero (X Y : ℤ) (A0 : ℚ_[p])
    (hroot : A0^2=(X:ℚ_[p])^2+(Y:ℚ_[p])^2) (hv : 0<A0.valuation) :
    (X:ZMod p)^2+(Y:ZMod p)^2=0 := by
  let u:=PadicUnitNormalization.integral A0 (le_of_lt hv)
  have hu : PadicInt.toZMod u=0:=PadicUnitNormalization.residue_zero_of_pos A0 hv
  have he : u^2=(X:ℤ_[p])^2+(Y:ℤ_[p])^2 := by
    apply Subtype.ext
    exact hroot
  have h:=congrArg PadicInt.toZMod he
  simp only [map_pow,map_add,map_intCast,hu] at h
  linear_combination -h

lemma integer_residue_zero (L : ℤ) (hv : 0<(L:ℚ_[p]).valuation) : (L:ZMod p)=0 := by
  have he : (L:ℤ_[p])=PadicUnitNormalization.integral (L:ℚ_[p]) (le_of_lt hv) := by
    apply Subtype.ext
    rfl
  have hz:=PadicUnitNormalization.residue_zero_of_pos (L:ℚ_[p]) hv
  rw [←he] at hz
  simpa only [map_intCast] using hz
end FourCorner.PrimitivePadicCoordinates
#print axioms FourCorner.PrimitivePadicCoordinates.coordinate_residues_nonzero
#print axioms FourCorner.PrimitivePadicCoordinates.norm_residue_zero
