import HasseUnitFifteenFactor
import HasseDyadicUnitFifteenModel

namespace FourCorner.HasseUnitFifteenSign

open HasseDyadicSymbol HasseDyadicAlgebra HasseConstantDyadic HasseDyadicUnitFifteenModel
open HasseUnitFifteenFactor HasseUnitFifteenNormalization HasseLocalUnits
open HasseRationalSource HasseAnchorChoice HasseTangentGlobal

noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem square_one_sub_s (s : ℚ_[2]) (hs : s ≠ 0) (hsv : 2≤s.valuation) : IsSquare (1-s^2) := by
  have hv : 3≤(-(s^2)).valuation := by rw [commonRoot_val_neg,Padic.valuation_pow];norm_num;omega
  simpa only [sub_eq_add_neg] using HasseUnitBranches.square_one_add_of_val_ge_three (-(s^2)) hv

/-- Exact evaluation in the oriented normalized unit-fifteen model, with all
square factors removed in the actual completed field. -/
theorem oriented_coefficient_sign (p Z s x y z : ℚ_[2])
    (hp0 : p ≠ 0) (hZ : Z ≠ 0) (hs : s ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsv : 2≤s.valuation) (hxv : x.valuation=0) (hyv : y.valuation=0) (hzv : z.valuation=0)
    (hpeq : p= -1+2*s^2)
    (heqx : (1-s^2)*x^2=(1-2*s^2)*(2*z^2-1))
    (heqy : (1-s^2)*y^2=1-2*s^2*z^2)
    (ho : PadicInt.toZModPow 2 ((normalizedUnit x hx : ℤ_[2])+(normalizedUnit y hy : ℤ_[2]))=0) :
    ∃ (hc : 2*(1-s^2) ≠ 0)
      (hF : coefficient p Z (s*x*Z) (2*s*y*Z) (2*s*z*Z) ≠ 0),
      dyadicSign (2*(1-s^2)) (coefficient p Z (s*x*Z) (2*s*y*Z) (2*s*z*Z)) hc hF=
        dyadicSign 2 (2*s*y) (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hs) hy)*
          (if s.valuation=2 then -1 else 1) := by
  obtain ⟨hN,hNsign⟩ := oriented_numerator_sign s x y z hs hx hy hz hsv hxv hyv hzv heqx heqy ho
  let N := HasseDyadicUnitFifteenModel.numerator s x y z
  let F := coefficient p Z (s*x*Z) (2*s*y*Z) (2*s*z*Z)
  have hs2v : (s^2).valuation=2*s.valuation := by rw [Padic.valuation_pow];norm_num
  obtain ⟨hA,hAv⟩ := one_sub_unit (s^2) (pow_ne_zero _ hs) (by omega)
  obtain ⟨r,hr⟩ := square_one_sub_s s hs hsv
  have hr2 : 1-s^2=r^2 := by simpa only [pow_two] using hr
  have hr0 : r ≠ 0 := by intro h;apply hA;simp [hr2,h]
  have hc : 2*(1-s^2) ≠ 0 := mul_ne_zero (by norm_num) hA
  have hscale : 2*p*s*Z*r ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp0) hs) hZ) hr0
  have hbase : 2*s*N ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hs) hN
  have hfactor : F=(2*s*N)*(2*p*s*Z*r)^2 := by
    dsimp [F]
    rw [coefficient_factor p Z s x y z hpeq heqx]
    change 8*p^2*s^3*(1-s^2)*Z^2*N=(2*s*N)*(2*p*s*Z*r)^2
    rw [hr2]
    ring
  have hF : F ≠ 0 := by rw [hfactor];exact mul_ne_zero hbase (pow_ne_zero _ hscale)
  have hleft : dyadicSign (2*(1-s^2)) F hc hF=dyadicSign 2 F (by norm_num) hF := by
    have hh := dyadicSign_mul_sq_left (2 : ℚ_[2]) F r (by norm_num) hF hr0
    simpa only [← hr2] using hh
  have hright : dyadicSign 2 F (by norm_num) hF=dyadicSign 2 (2*s*N) (by norm_num) hbase := by
    have hh := dyadicSign_mul_sq_right (2 : ℚ_[2]) (2*s*N) (2*p*s*Z*r) (by norm_num) hbase hscale
    simpa only [← hfactor] using hh
  have hySign := dyadicSign_two_y s y z hs hy hz hsv hyv hzv heqy
  have hWsign : dyadicSign 2 (2*s*y) (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hs) hy)=
      dyadicSign 2 (2*s) (by norm_num) (mul_ne_zero (by norm_num) hs) := by
    rw [dyadicSign_mul_right (2 : ℚ_[2]) (2*s) y (by norm_num) (mul_ne_zero (by norm_num) hs) hy,hySign,mul_one]
  refine ⟨hc,hF,?_⟩
  rw [hleft,hright,dyadicSign_mul_right (2 : ℚ_[2]) (2*s) N (by norm_num)
    (mul_ne_zero (by norm_num) hs) hN,hWsign,hNsign]

theorem dyadicSign_two_two : dyadicSign (2 : ℚ_[2]) 2 (by norm_num) (by norm_num)=1 := by
  have hr : residue8 (2 : ℚ_[2]) (by norm_num)=1 := by simpa using residue8_qpow 1
  rw [dyadicSign,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,hr]
  decide

theorem source_coefficient_flip (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) (D : TangentData p P)
    (hcb : dyadicSign (firstCoefficient p : ℚ_[2]) ((p : ℚ_[2])+1)
      (by exact_mod_cast (ne_of_lt (firstCoefficient_negative p hp))) (by exact_mod_cast (show p+1 ≠ 0 by linarith))=1) :
    ∃ hF' : coefficient (p : ℚ_[2]) (P.Z : ℚ_[2]) (-(P.U : ℚ_[2])) (D.w : ℚ_[2]) (P.T : ℚ_[2]) ≠ 0,
      dyadicSign (firstCoefficient p : ℚ_[2]) (secondCoefficient p P D : ℚ_[2])
        (by exact_mod_cast (ne_of_lt (firstCoefficient_negative p hp))) (by exact_mod_cast (ne_of_lt D.coefficient_negative))=
      dyadicSign (firstCoefficient p : ℚ_[2])
        (coefficient (p : ℚ_[2]) (P.Z : ℚ_[2]) (-(P.U : ℚ_[2])) (D.w : ℚ_[2]) (P.T : ℚ_[2]))
        (by exact_mod_cast (ne_of_lt (firstCoefficient_negative p hp))) hF' := by
  have hP : ((p : ℚ_[2])-1)*(P.U : ℚ_[2])^2-(p : ℚ_[2])*(P.T : ℚ_[2])^2+
      (p : ℚ_[2])*((p : ℚ_[2])+1)*(P.Z : ℚ_[2])^2=0 := by
    have hh : (p-1)*P.U^2-p*P.T^2+p*(p+1)*P.Z^2=0 := by linear_combination -P.equations.2.2
    exact_mod_cast hh
  have hQ : ((p : ℚ_[2])-1)*(anchorU p P.Z D.w P.T : ℚ_[2])^2-
      (p : ℚ_[2])*(anchorT p P.Z D.w P.T : ℚ_[2])^2+
      (p : ℚ_[2])*((p : ℚ_[2])+1)*(anchorZ p P.Z D.w : ℚ_[2])^2=0 := by
    have hh := CompleteSource11.anchor_conic p P.Z P.V D.w P.T D.omission
    change (p-1)*(anchorU p P.Z D.w P.T)^2-p*(anchorT p P.Z D.w P.T)^2+
      p*(p+1)*(anchorZ p P.Z D.w)^2=0 at hh
    exact_mod_cast hh
  have hsep : (anchorT p P.Z D.w P.T : ℚ_[2])*(P.Z : ℚ_[2])-
      (anchorZ p P.Z D.w : ℚ_[2])*(P.T : ℚ_[2]) ≠ 0 := by
    have hn : (separation p P.Z D.w P.T : ℚ_[2]) ≠ 0 := by exact_mod_cast D.separated
    intro hh
    apply hn
    dsimp [separation]
    push_cast
    linear_combination -hh
  obtain ⟨hF,hF',hSign⟩ := dyadicSign_polar_flip (p : ℚ_[2]) (P.Z : ℚ_[2]) (P.U : ℚ_[2]) (P.T : ℚ_[2])
    (anchorZ p P.Z D.w : ℚ_[2]) (anchorU p P.Z D.w P.T : ℚ_[2]) (anchorT p P.Z D.w P.T : ℚ_[2])
    (firstCoefficient p : ℚ_[2]) (by exact_mod_cast (show p ≠ 0 by linarith))
    (by exact_mod_cast (show p+1 ≠ 0 by linarith)) (by exact_mod_cast (ne_of_lt (firstCoefficient_negative p hp)))
    hP hQ hsep hcb
  have hOrig : -(p : ℚ_[2])*(((p : ℚ_[2])-1)*(anchorU p P.Z D.w P.T : ℚ_[2])*(P.U : ℚ_[2])-
      (p : ℚ_[2])*(anchorT p P.Z D.w P.T : ℚ_[2])*(P.T : ℚ_[2])+
      (p : ℚ_[2])*((p : ℚ_[2])+1)*(anchorZ p P.Z D.w : ℚ_[2])*(P.Z : ℚ_[2]))=
      (secondCoefficient p P D : ℚ_[2]) := by
    dsimp [secondCoefficient,secondPolar]
    push_cast
    ring
  have hFlip : -(p : ℚ_[2])*(-((p : ℚ_[2])-1)*(anchorU p P.Z D.w P.T : ℚ_[2])*(P.U : ℚ_[2])-
      (p : ℚ_[2])*(anchorT p P.Z D.w P.T : ℚ_[2])*(P.T : ℚ_[2])+
      (p : ℚ_[2])*((p : ℚ_[2])+1)*(anchorZ p P.Z D.w : ℚ_[2])*(P.Z : ℚ_[2]))=
      coefficient (p : ℚ_[2]) (P.Z : ℚ_[2]) (-(P.U : ℚ_[2])) (D.w : ℚ_[2]) (P.T : ℚ_[2]) := by
    dsimp [coefficient,anchorU,anchorT,anchorZ]
    push_cast
    ring
  simp only [hOrig,hFlip] at hF hF' hSign
  exact ⟨hF',hSign⟩

#print axioms oriented_coefficient_sign
#print axioms source_coefficient_flip

end
end FourCorner.HasseUnitFifteenSign
