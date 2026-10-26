import HasseParameterSupport

namespace FourCorner.HasseSignAlgebra

open HilbertArithmeticHigh11 HilbertWellDefinedHigh11 HasseHilbertArithmetic

/-- Bilinearity for the actual nonzero rational coefficients of the proved
arithmetic Hilbert sign, rather than an assumed symbol law. -/
theorem rationalSign_mul_left (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (v : ℕ) :
    rationalSign (a*b) c (mul_ne_zero ha hb) hc v=
      rationalSign a c ha hc v*rationalSign b c hb hc v := by
  let xs := primePresentation a ha
  let ys := primePresentation b hb
  let zs := primePresentation c hc
  let s := squareScale a ha
  let t := squareScale b hb
  let u := squareScale c hc
  have hs := (squareScale_spec a ha).1
  have ht := (squareScale_spec b hb).1
  have hu := (squareScale_spec c hc).1
  have he : a*b=evalPresentation (xs++ys)*(s*t)^2 := by
    rw [evalPresentation_append,(squareScale_spec a ha).2,(squareScale_spec b hb).2]
    ring
  rw [rationalSign_eq_presentation (a*b) c (mul_ne_zero ha hb) hc (xs++ys) zs (s*t) u
    (mul_ne_zero hs ht) hu he (squareScale_spec c hc).2 v]
  exact presentationSign_append_left xs ys zs v

theorem rationalSign_mul_right (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (v : ℕ) :
    rationalSign a (b*c) ha (mul_ne_zero hb hc) v=
      rationalSign a b ha hb v*rationalSign a c ha hc v := by
  rw [rationalSign_symm,rationalSign_mul_left,rationalSign_symm b a,rationalSign_symm c a]

theorem rationalSign_square_left (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (v : ℕ) :
    rationalSign (a^2) b (pow_ne_zero _ ha) hb v=1 := by
  rw [rationalSign_eq_presentation (a^2) b (pow_ne_zero _ ha) hb [] (primePresentation b hb)
    a (squareScale b hb) ha (squareScale_spec b hb).1
    (by simp [evalPresentation]) (squareScale_spec b hb).2 v]
  rfl

theorem rationalSign_square_right (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (v : ℕ) :
    rationalSign a (b^2) ha (pow_ne_zero _ hb) v=1 := by
  rw [rationalSign_symm,rationalSign_square_left b a hb ha v]

theorem rationalSign_mul_square_right (a b s : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (v : ℕ) :
    rationalSign a (b*s^2) ha (mul_ne_zero hb (pow_ne_zero _ hs)) v=rationalSign a b ha hb v := by
  rw [rationalSign_mul_right a b (s^2) ha hb (pow_ne_zero _ hs) v,
    rationalSign_square_right a s ha hs v,mul_one]

theorem rationalSign_mul_square_left (a b s : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (v : ℕ) :
    rationalSign (a*s^2) b (mul_ne_zero ha (pow_ne_zero _ hs)) hb v=rationalSign a b ha hb v := by
  rw [rationalSign_mul_left a (s^2) b ha (pow_ne_zero _ hs) hb v,
    rationalSign_square_left s b hs hb v,mul_one]

def bitSign (x : ZMod 2) : ℤ := (-1)^x.val

theorem bitSign_add : ∀ x y : ZMod 2, bitSign (x+y)=bitSign x*bitSign y := by decide

theorem bitSign_zero : bitSign 0=1 := rfl

theorem bitSign_one : bitSign 1= -1 := rfl

theorem bitSign_sum {ι : Type*} (S : Finset ι) (f : ι → ZMod 2) :
    bitSign (∑ i ∈ S,f i)=∏ i ∈ S,bitSign (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty,bitSign_zero]
  | @insert i S hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,bitSign_add,ih]

theorem bitSign_injective : Function.Injective bitSign := by
  decide

#print axioms rationalSign_mul_left
#print axioms rationalSign_mul_right
#print axioms rationalSign_mul_square_right
#print axioms rationalSign_mul_square_left
#print axioms bitSign_sum
#print axioms bitSign_injective

end FourCorner.HasseSignAlgebra
