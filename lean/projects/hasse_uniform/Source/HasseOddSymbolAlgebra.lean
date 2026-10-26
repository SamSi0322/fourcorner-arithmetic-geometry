import HasseEvenPole
namespace FourCorner.HasseOddSymbolAlgebra
open HilbertArithmeticHigh11 HasseOddSymbol HasseLocalUnits HasseHilbertArithmetic

/-- Multiplication of actual completed-field second entries, proved from
normalized residues and the all-depth odd formula. -/
theorem oddSign_mul_right (Q : OddPrime) (x y z : ℚ_[Q.val])
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    oddSign Q x (y*z) hx (mul_ne_zero hy hz)=oddSign Q x y hx hy*oddSign Q x z hx hz := by
  have hcx := quadraticChar_sq_one (residue_ne_zero x hx)
  change (quadraticCharFun (ZMod Q.val) (residue x hx))^2=1 at hcx
  have hn : (-1 : ℤ)^(Q.val/2*2)=1 := by rw [Nat.mul_comm _ 2,pow_mul]; norm_num
  have hres : quadraticChar (ZMod Q.val) (residue (y*z) (mul_ne_zero hy hz))=
      quadraticChar (ZMod Q.val) (residue y hy)*quadraticChar (ZMod Q.val) (residue z hz) := by
    rw [residue_mul y z hy hz,map_mul]
  simp only [oddSign,Padic.valuation_mul hy hz,Int.cast_add,hres,ZMod.val_add]
  have hxa := ZMod.val_lt (x.valuation : ZMod 2)
  have hya := ZMod.val_lt (y.valuation : ZMod 2)
  have hza := ZMod.val_lt (z.valuation : ZMod 2)
  generalize ((x.valuation : ZMod 2).val)=a at *
  generalize ((y.valuation : ZMod 2).val)=b at *
  generalize ((z.valuation : ZMod 2).val)=c at *
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    norm_num [mul_pow,pow_add,pow_mul,hcx] <;> ring_nf <;> simp only [hcx,hn,mul_one]

/-- A completed square may be removed from the second entry without any
rationality restriction on its square root. -/
theorem oddSign_one_of_right_square (Q : OddPrime) (x y : ℚ_[Q.val])
    (hx : x ≠ 0) (hy : y ≠ 0) (hsq : IsSquare y) : oddSign Q x y hx hy=1 := by
  obtain ⟨s,hs⟩ := hsq
  have he : y=s^2 := by simpa only [pow_two] using hs
  have hs0 : s ≠ 0 := by intro hh; apply hy; simp [he,hh]
  have hv : (y.valuation : ZMod 2)=0 := by
    rw [he,Padic.valuation_pow]
    push_cast
    simp only [show (2 : ZMod 2)=0 by decide,zero_mul]
  have hr : IsSquare (residue y hy) := by
    have hh : residue y hy=(residue s hs0)^2 := by simpa only [← he] using residue_sq s hs0
    rw [hh]
    exact IsSquare.sq _
  have hc : quadraticChar (ZMod Q.val) (residue y hy)=1 :=
    (quadraticChar_one_iff_isSquare (residue_ne_zero y hy)).mpr hr
  simp only [oddSign,hv,ZMod.val_zero,zero_mul,mul_zero,pow_zero,one_mul,hc,one_pow,mul_one]

theorem oddSign_sq_one (Q : OddPrime) (x y : ℚ_[Q.val]) (hx : x ≠ 0) (hy : y ≠ 0) :
    (oddSign Q x y hx hy)^2=1 := by
  have hh := oddSign_one_of_right_square Q x (y*y) hx (mul_ne_zero hy hy) ⟨y,rfl⟩
  rw [oddSign_mul_right] at hh
  simpa only [pow_two] using hh

/-- Actual local squareclass invariance follows from multiplicativity. -/
theorem oddSign_eq_of_square_ratio (Q : OddPrime) (x y z : ℚ_[Q.val])
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hs : IsSquare (y/z)) :
    oddSign Q x y hx hy=oddSign Q x z hx hz := by
  have hn : y/z ≠ 0 := div_ne_zero hy hz
  have hh := oddSign_mul_right Q x (y/z) z hx hn hz
  have heq : y/z*z=y := div_mul_cancel₀ y hz
  simp only [heq,oddSign_one_of_right_square Q _ _ hx hn hs,one_mul] at hh
  exact hh

#print axioms oddSign_mul_right
#print axioms oddSign_one_of_right_square
#print axioms oddSign_sq_one
#print axioms oddSign_eq_of_square_ratio
end FourCorner.HasseOddSymbolAlgebra
