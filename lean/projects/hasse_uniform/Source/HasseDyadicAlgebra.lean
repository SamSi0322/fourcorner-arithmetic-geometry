import HasseDyadicNonunit

namespace FourCorner.HasseDyadicAlgebra
open HasseDyadicSymbol HasseAnchorChoice CompleteSource11

noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem formula_mul_right : ∀ (r s s' : ZMod 2) (u v v' : ZMod 8),
    HilbertDyadicFormulaHigh11.OddUnit u → HilbertDyadicFormulaHigh11.OddUnit v →
    HilbertDyadicFormulaHigh11.OddUnit v' →
    HilbertDyadicFormulaHigh11.formula r u (s+s') (v*v')=
      HilbertDyadicFormulaHigh11.formula r u s v*HilbertDyadicFormulaHigh11.formula r u s' v' := by
  decide

private theorem formula_mul_left : ∀ (r r' s : ZMod 2) (u u' v : ZMod 8),
    HilbertDyadicFormulaHigh11.OddUnit u → HilbertDyadicFormulaHigh11.OddUnit u' →
    HilbertDyadicFormulaHigh11.OddUnit v →
    HilbertDyadicFormulaHigh11.formula (r+r') (u*u') s v=
      HilbertDyadicFormulaHigh11.formula r u s v*HilbertDyadicFormulaHigh11.formula r' u' s v := by
  decide

theorem dyadicSign_mul_right (x y z : ℚ_[2]) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    dyadicSign x (y*z) hx (mul_ne_zero hy hz)=dyadicSign x y hx hy*dyadicSign x z hx hz := by
  simp only [dyadicSign,Padic.valuation_mul hy hz,Int.cast_add,residue8_mul y z hy hz]
  exact formula_mul_right _ _ _ _ _ _ (residue8_odd x hx) (residue8_odd y hy) (residue8_odd z hz)

theorem dyadicSign_mul_left (x y z : ℚ_[2]) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    dyadicSign (x*y) z (mul_ne_zero hx hy) hz=dyadicSign x z hx hz*dyadicSign y z hy hz := by
  simp only [dyadicSign,Padic.valuation_mul hx hy,Int.cast_add,residue8_mul x y hx hy]
  exact formula_mul_left _ _ _ _ _ _ (residue8_odd x hx) (residue8_odd y hy) (residue8_odd z hz)

theorem dyadicSign_sq_one (x y : ℚ_[2]) (hx : x ≠ 0) (hy : y ≠ 0) :
    (dyadicSign x y hx hy)^2=1 := by
  have hf : ∀ (r s : ZMod 2) (u v : ZMod 8),
      (HilbertDyadicFormulaHigh11.formula r u s v)^2=1 := by decide
  exact hf _ _ _ _

/-- The two source-U signs have an exact square product times b. This is a
polynomial identity on the original conic, before any sign evaluation. -/
theorem polar_flip_product (p Z U T z u t : ℚ_[2])
    (hP : (p-1)*U^2-p*T^2+p*(p+1)*Z^2=0)
    (hQ : (p-1)*u^2-p*t^2+p*(p+1)*z^2=0) :
    ((p-1)*u*U-p*t*T+p*(p+1)*z*Z)*
      (-(p-1)*u*U-p*t*T+p*(p+1)*z*Z)=
      p^2*(p+1)*(t*Z-z*T)^2 := by
  linear_combination -(p-1)*u^2*hP - (p*T^2-p*(p+1)*Z^2)*hQ

/-- A proved algebraic sign comparison on U and −U. It requires the exact
sign of b and the nonzero original separation; it is not evaluation constancy. -/
theorem dyadicSign_polar_flip (p Z U T z u t c : ℚ_[2])
    (hp : p ≠ 0) (hb : p+1 ≠ 0) (hc : c ≠ 0)
    (hP : (p-1)*U^2-p*T^2+p*(p+1)*Z^2=0)
    (hQ : (p-1)*u^2-p*t^2+p*(p+1)*z^2=0)
    (hsep : t*Z-z*T ≠ 0) (hcb : dyadicSign c (p+1) hc hb=1) :
    ∃ (hL : -p*((p-1)*u*U-p*t*T+p*(p+1)*z*Z) ≠ 0)
      (hL' : -p*(-(p-1)*u*U-p*t*T+p*(p+1)*z*Z) ≠ 0),
      dyadicSign c (-p*((p-1)*u*U-p*t*T+p*(p+1)*z*Z)) hc hL=
        dyadicSign c (-p*(-(p-1)*u*U-p*t*T+p*(p+1)*z*Z)) hc hL' := by
  let L := -p*((p-1)*u*U-p*t*T+p*(p+1)*z*Z)
  let M := -p*(-(p-1)*u*U-p*t*T+p*(p+1)*z*Z)
  have he : L*M=(p+1)*(p^2*(t*Z-z*T))^2 := by
    have hh := polar_flip_product p Z U T z u t hP hQ
    dsimp [L,M]
    linear_combination p^2*hh
  have hs : p^2*(t*Z-z*T) ≠ 0 := mul_ne_zero (pow_ne_zero _ hp) hsep
  have hLM : L*M ≠ 0 := by rw [he]; exact mul_ne_zero hb (pow_ne_zero _ hs)
  have hL := (mul_ne_zero_iff.mp hLM).1
  have hM := (mul_ne_zero_iff.mp hLM).2
  refine ⟨hL,hM,?_⟩
  have hprod : dyadicSign c L hc hL*dyadicSign c M hc hM=1 := by
    rw [← dyadicSign_mul_right]
    have hh := dyadicSign_mul_sq_right c (p+1) (p^2*(t*Z-z*T)) hc hb hs
    rw [hcb] at hh
    simpa only [← he] using hh
  have hsq := dyadicSign_sq_one c M hc hM
  change dyadicSign c L hc hL=dyadicSign c M hc hM
  apply (mul_right_cancel₀ (show dyadicSign c M hc hM ≠ 0 by intro hz; simp [hz] at hsq))
  exact hprod.trans (by simpa only [pow_two] using hsq.symm)

#print axioms dyadicSign_mul_right
#print axioms dyadicSign_mul_left
#print axioms dyadicSign_sq_one
#print axioms polar_flip_product
#print axioms dyadicSign_polar_flip
end
end FourCorner.HasseDyadicAlgebra
