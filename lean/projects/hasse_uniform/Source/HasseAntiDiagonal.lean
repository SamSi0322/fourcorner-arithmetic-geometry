import HasseSignAlgebra

namespace FourCorner.HasseAntiDiagonal

open HilbertArithmeticHigh11 HilbertWellDefinedHigh11 HasseSignAlgebra HasseHilbertArithmetic

theorem presentationSign_sq_one (xs ys : List Atom) (v : ℕ) : (presentationSign xs ys v)^2=1 := by
  have hh := square_eval_sign (xs++xs) ys (evalPresentation xs)
    (HilbertOddFormulaHigh11.evalPresentation_ne_zero xs)
    (by rw [evalPresentation_append,pow_two]) v
  simpa only [presentationSign_append_left,pow_two] using hh

theorem generator_self (x : Atom) (v : ℕ) : generatorSign x x v=generatorSign x Atom.negOne v := by
  cases x with
  | negOne => rfl
  | two => rfl
  | prime p => simp only [generatorSign,if_true]

theorem presentation_diagonal (xs : List Atom) (v : ℕ) :
    presentationSign xs xs v=presentationSign xs [Atom.negOne] v := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hcross : presentationSign xs (x::xs) v=rowSign x xs v*presentationSign xs xs v := by
      rw [presentationSign_symm]
      rfl
    have hs : (rowSign x xs v)^2=1 := by
      simpa only [presentationSign,mul_one] using presentationSign_sq_one [x] xs v
    rw [presentationSign,rowSign,hcross,ih,generator_self]
    change generatorSign x Atom.negOne v*rowSign x xs v*
      (rowSign x xs v*presentationSign xs [Atom.negOne] v)=
      (generatorSign x Atom.negOne v*1)*presentationSign xs [Atom.negOne] v
    calc
      _=generatorSign x Atom.negOne v*(rowSign x xs v)^2*presentationSign xs [Atom.negOne] v := by ring
      _=_ := by rw [hs]

theorem rationalSign_diagonal (a : ℚ) (ha : a ≠ 0) (v : ℕ) :
    rationalSign a a ha ha v=rationalSign a (-1) ha (by norm_num) v := by
  rw [rationalSign_eq_presentation a (-1) ha (by norm_num) (primePresentation a ha) [Atom.negOne]
    (squareScale a ha) 1 (squareScale_spec a ha).1 one_ne_zero (squareScale_spec a ha).2
    (by norm_num [evalPresentation,value]) v]
  exact presentation_diagonal _ _

/-- The anti-diagonal Hilbert identity is proved from the literal generator
formulas and square invariance, not imported as an unproved norm criterion. -/
theorem rationalSign_antidiagonal (a : ℚ) (ha : a ≠ 0) (v : ℕ) :
    rationalSign a (-a) ha (neg_ne_zero.mpr ha) v=1 := by
  have hh := rationalSign_mul_right a a (-1) ha ha (by norm_num) v
  have hh' : rationalSign a (-a) ha (neg_ne_zero.mpr ha) v=
      rationalSign a a ha ha v*rationalSign a (-1) ha (by norm_num) v := by
    simpa only [mul_neg_one] using hh
  rw [hh',rationalSign_diagonal]
  simpa only [pow_two] using rationalSign_sq_one a (-1) ha (by norm_num) v

#print axioms presentation_diagonal
#print axioms rationalSign_antidiagonal

end FourCorner.HasseAntiDiagonal
