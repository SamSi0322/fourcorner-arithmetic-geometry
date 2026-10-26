import HasseDyadicIntegralSign

namespace FourCorner.HasseDyadicUnitOneFlip
open HasseDyadicSymbol HasseDyadicAlgebra HasseDyadicNonunit HasseDyadicUnitOneNormalization
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem numerator_product (s x y t : ℚ_[2])
    (hx : x^2=(1+2*s^2)*(2*t^2-(1+s^2)))
    (hy : y^2=(1+s^2)*(2*t^2-1)) :
    (1+s^2)*numerator (1+2*s^2) s x y t*numerator (1+2*s^2) s (-x) y t=
      2*(s*(y*(1+s^2+t)+(1+s^2)*s*(2*t+1)))^2 := by
  dsimp [numerator]
  linear_combination -(1+s^2)*(y+s*(2*t+1))^2*hx+
    (1+2*s^2)*(1+s^2-2*t^2)*hy

theorem numerator_flip_sign (s x y t : ℚ_[2]) (hs : s ≠ 0) (hsv : 2 ≤ s.valuation)
    (hx : x^2=(1+2*s^2)*(2*t^2-(1+s^2)))
    (hy : y^2=(1+s^2)*(2*t^2-1))
    (hL : y*(1+s^2+t)+(1+s^2)*s*(2*t+1) ≠ 0) :
    ∃ (hH : -numerator (1+2*s^2) s x y t ≠ 0)
      (hM : -numerator (1+2*s^2) s (-x) y t ≠ 0),
      dyadicSign (-2) (-numerator (1+2*s^2) s x y t) (by norm_num) hH=
        dyadicSign (-2) (-numerator (1+2*s^2) s (-x) y t) (by norm_num) hM := by
  let A := 1+s^2
  let H := numerator (1+2*s^2) s x y t
  let M := numerator (1+2*s^2) s (-x) y t
  let L := y*(1+s^2+t)+(1+s^2)*s*(2*t+1)
  have hprod : A*H*M=2*(s*L)^2 := numerator_product s x y t hx hy
  have hR : 2*(s*L)^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero hs hL))
  have hleft : A*H*M ≠ 0 := by rw [hprod]; exact hR
  have hA : A ≠ 0 := ((mul_ne_zero_iff.mp hleft).1 |> mul_ne_zero_iff.mp).1
  have hH : H ≠ 0 := ((mul_ne_zero_iff.mp hleft).1 |> mul_ne_zero_iff.mp).2
  have hM : M ≠ 0 := (mul_ne_zero_iff.mp hleft).2
  have hsqA : IsSquare A := by
    exact square_one_add_of_val_ge_three (s^2) (pow_ne_zero _ hs)
      (by rw [Padic.valuation_pow]; norm_num; omega)
  obtain ⟨r,hr⟩ := hsqA
  have hr2 : A=r^2 := by simpa only [pow_two] using hr
  have hr0 : r ≠ 0 := by intro h; apply hA; simp [hr2,h]
  have hf : (-H)*(-M)=2*(s*L/r)^2 := by
    apply (mul_left_cancel₀ hA)
    field_simp [hr0]
    rw [hr2] at hprod
    linear_combination hprod
  have hscale : s*L/r ≠ 0 := div_ne_zero (mul_ne_zero hs hL) hr0
  have hbase : dyadicSign (-2 : ℚ_[2]) 2 (by norm_num) (by norm_num)=1 := by
    have hnv : (-2 : ℚ_[2]).valuation=1 := by
      rw [show (-2 : ℚ_[2])= -(2 : ℚ_[2]) by ring,commonRoot_val_neg]
      exact Padic.valuation_p
    have h2 : residue8 (2 : ℚ_[2]) (by norm_num)=1 := by simpa using residue8_qpow 1
    rw [dyadicSign,hnv,residue8_negTwo,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,h2]
    decide
  have hsignprod : dyadicSign (-2) (-H) (by norm_num) (neg_ne_zero.mpr hH)*
      dyadicSign (-2) (-M) (by norm_num) (neg_ne_zero.mpr hM)=1 := by
    rw [← dyadicSign_mul_right]
    have hh := dyadicSign_mul_sq_right (-2 : ℚ_[2]) 2 (s*L/r) (by norm_num) (by norm_num) hscale
    rw [hbase] at hh
    simpa only [← hf] using hh
  refine ⟨neg_ne_zero.mpr hH,neg_ne_zero.mpr hM,?_⟩
  change dyadicSign (-2) (-H) (by norm_num) (neg_ne_zero.mpr hH)=
    dyadicSign (-2) (-M) (by norm_num) (neg_ne_zero.mpr hM)
  have hsq := dyadicSign_sq_one (-2) (-M) (by norm_num) (neg_ne_zero.mpr hM)
  apply (mul_right_cancel₀ (show dyadicSign (-2) (-M) (by norm_num) (neg_ne_zero.mpr hM) ≠ 0 by
    intro hz; simp [hz] at hsq))
  exact hsignprod.trans (by simpa only [pow_two] using hsq.symm)

#print axioms numerator_product
#print axioms numerator_flip_sign
end
end FourCorner.HasseDyadicUnitOneFlip
