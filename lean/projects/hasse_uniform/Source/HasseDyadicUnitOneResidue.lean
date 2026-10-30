import HasseDyadicUnitFinite
import HasseDyadicUnitOneNormalization

namespace FourCorner.HasseDyadicUnitOneResidue
open HasseDyadicUnitFinite

noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def modelNumerator (S X Y T : ℤ_[2]) : ℤ_[2] :=
  X*Y+(4*S)*(2*T+1)*(X+Y)+2*(1+2*(4*S)^2)*T^2+
    2*(4*S)^2*T-(1+(4*S)^2)

/-- Exact residue of the literal original-source numerator in its integral
unit-one gauge, after a proved U-sign orientation. Arbitrarily large v₂(s)
is retained by the unrestricted dyadic integer S=s/4. -/
theorem source_model_residue (S X Y T : ℤ_[2]) (hT : ‖T‖=1)
    (hX : X^2=(1+2*(4*S)^2)*(2*T^2-(1+(4*S)^2)))
    (hY : Y^2=(1+(4*S)^2)*(2*T^2-1))
    (hXY : PadicInt.toZModPow 2 (X*Y)=1) :
    PadicInt.toZModPow 4 (modelNumerator S X Y T)=2+8*PadicInt.toZModPow 4 S := by
  let r := PadicInt.toZModPow 5 (p:=2)
  have hTnz := (dyadic_norm_one_iff_residue_ne_zero T).mp hT
  have hTc := PadicInt.cast_toZModPow (p:=2) 1 5 (by decide) T
  have hTodd : odd32 (r T) := by
    have hf : ∀ t : ZMod 32, (ZMod.cast t : ZMod 2) ≠ 0 → odd32 t := by decide
    exact hf _ (by simpa only [← hTc] using hTnz)
  have hXp := congrArg r hX
  have hYp := congrArg r hY
  simp only [map_pow,map_add,map_mul,map_sub,map_one,map_ofNat] at hXp hYp
  have hp : (1 : ZMod 32)+2*(4*r S)^2=1 := by
    have hf : ∀ s : ZMod 32, 1+2*(4*s)^2=1 := by decide
    exact hf _
  rw [hp,one_mul] at hXp
  have hXYp : mod4 (r X*r Y)=1 := by
    have hc := PadicInt.cast_toZModPow (p:=2) 2 5 (by decide) (X*Y)
    rw [hXY] at hc
    change (ZMod.cast (r X*r Y) : ZMod 4)=1
    simpa only [r,map_mul] using hc
  have hh := unitOne_tangent_numerator (r S) (r X) (r Y) (r T) hTodd (by simpa only [sub_add_eq_sub_sub] using hXp) hYp hXYp
  have hn : PadicInt.toZModPow 4 (modelNumerator S X Y T)=
      mod16 (r (modelNumerator S X Y T)) := by
    symm
    simpa only [mod16,ZMod.castHom_apply] using
      PadicInt.cast_toZModPow (p:=2) 4 5 (by decide) (modelNumerator S X Y T)
  rw [hn]
  have hs : mod16 (r S)=PadicInt.toZModPow 4 S := by
    simpa only [mod16,ZMod.castHom_apply] using PadicInt.cast_toZModPow (p:=2) 4 5 (by decide) S
  rw [← hs]
  simpa only [modelNumerator,map_mul,map_add,map_sub,map_pow,map_one,map_ofNat] using hh

#print axioms source_model_residue
end
end FourCorner.HasseDyadicUnitOneResidue
