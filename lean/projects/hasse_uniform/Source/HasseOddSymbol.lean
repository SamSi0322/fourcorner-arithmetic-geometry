import HasseLocalUnits

/-! The standard odd Hilbert-sign formula on actual Q_q, and its proved
comparison with the rational arithmetic sign used in global reciprocity. -/
namespace FourCorner.HasseOddSymbol

open HilbertArithmeticHigh11 HilbertWellDefinedHigh11 HasseLocalUnits

noncomputable def oddSign (q : OddPrime) (x y : ℚ_[q.val]) (hx : x ≠ 0) (hy : y ≠ 0) : ℤ :=
  (-1)^(((x.valuation : ZMod 2).val)*((y.valuation : ZMod 2).val)*(q.val/2))*
    (quadraticChar (ZMod q.val) (residue x hx))^((y.valuation : ZMod 2).val)*
    (quadraticChar (ZMod q.val) (residue y hy))^((x.valuation : ZMod 2).val)

private theorem pow_mod_two {z : ℤ} (hz : z^2=1) (n : ℕ) : z^n=z^(n%2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2]
  rw [pow_add,pow_mul,hz,one_pow,mul_one]

/-- This proves the actual all-depth completed-field comparison, including
negative valuations, without assuming that the arithmetic sign is a symbol. -/
theorem rationalSign_eq_oddSign (q : OddPrime) (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    rationalSign a b ha hb q.val=oddSign q (a : ℚ_[q.val]) (b : ℚ_[q.val])
      (by exact_mod_cast ha) (by exact_mod_cast hb) := by
  let xs := primePresentation a ha
  let ys := primePresentation b hb
  have hvx : (((a : ℚ_[q.val]).valuation : ℤ) : ZMod 2)=
      (HilbertOddFormulaHigh11.order q xs : ZMod 2) := by
    rw [Padic.valuation_ratCast,HilbertOddFormulaHigh11.rational_presentation_valuation q xs
      (squareScale a ha) a (squareScale_spec a ha).1 (squareScale_spec a ha).2]
    push_cast
    simp only [show (2 : ZMod 2)=0 by decide,zero_mul,add_zero]
  have hvy : (((b : ℚ_[q.val]).valuation : ℤ) : ZMod 2)=
      (HilbertOddFormulaHigh11.order q ys : ZMod 2) := by
    rw [Padic.valuation_ratCast,HilbertOddFormulaHigh11.rational_presentation_valuation q ys
      (squareScale b hb) b (squareScale_spec b hb).1 (squareScale_spec b hb).2]
    push_cast
    simp only [show (2 : ZMod 2)=0 by decide,zero_mul,add_zero]
  have hcx := quadraticChar_rational_residue q xs (squareScale a ha) a
    (squareScale_spec a ha).1 (squareScale_spec a ha).2 (by exact_mod_cast ha)
  have hcy := quadraticChar_rational_residue q ys (squareScale b hb) b
    (squareScale_spec b hb).1 (squareScale_spec b hb).2 (by exact_mod_cast hb)
  have hfirst : (-1 : ℤ)^(HilbertOddFormulaHigh11.order q xs*HilbertOddFormulaHigh11.order q ys*(q.val/2)) =
      (-1 : ℤ)^((HilbertOddFormulaHigh11.order q xs%2)*(HilbertOddFormulaHigh11.order q ys%2)*(q.val/2)) := by
    rw [neg_one_pow_eq_pow_mod_two,
      neg_one_pow_eq_pow_mod_two ((HilbertOddFormulaHigh11.order q xs%2)*(HilbertOddFormulaHigh11.order q ys%2)*(q.val/2))]
    congr 1
    simp only [Nat.mul_mod,Nat.mod_mod]
  change presentationSign xs ys q.val=_
  rw [HilbertOddFormulaHigh11.presentation_odd_formula]
  simp only [oddSign,hvx,hvy,hcx,hcy,ZMod.val_natCast,HilbertOddFormulaHigh11.formula]
  rw [hfirst,pow_mod_two (legendreSym.sq_one q.val
    (HilbertOddFormulaHigh11.unit_residue_nonzero q xs)),
    pow_mod_two (legendreSym.sq_one q.val (HilbertOddFormulaHigh11.unit_residue_nonzero q ys))]

/-- The actual odd-completion symbol vanishes on a square first coefficient.
The proof uses its valuation and the literal square normalized residue. -/
theorem oddSign_one_of_left_square (q : OddPrime) (x y : ℚ_[q.val])
    (hx : x ≠ 0) (hy : y ≠ 0) (hsq : IsSquare x) : oddSign q x y hx hy=1 := by
  obtain ⟨s,hs⟩ := hsq
  have he : x=s^2 := by simpa only [pow_two] using hs
  have hs0 : s ≠ 0 := by intro hh; apply hx; simp [he,hh]
  have hv : (x.valuation : ZMod 2)=0 := by
    rw [he,Padic.valuation_pow]
    push_cast
    simp only [show (2 : ZMod 2)=0 by decide,zero_mul]
  have hr : IsSquare (residue x hx) := by
    have hh : residue x hx=(residue s hs0)^2 := by
      simpa only [← he] using residue_sq s hs0
    rw [hh]
    exact IsSquare.sq _
  have hc : quadraticChar (ZMod q.val) (residue x hx)=1 :=
    (quadraticChar_one_iff_isSquare (residue_ne_zero x hx)).mpr hr
  simp only [oddSign,hv,ZMod.val_zero,zero_mul,mul_zero,pow_zero,one_mul,hc,one_pow,mul_one]

/-- The square lifting used by the positive-p and split positive-b rows,
over the actual completed field and at arbitrary positive depth. -/
theorem square_of_positive_perturbation (q : OddPrime) (x y : ℚ_[q.val])
    (hx : x ≠ 0) (hvx : x.valuation=0) (hsq : IsSquare x)
    (hneq : y-x ≠ 0) (hsmall : 0<(y-x).valuation) : IsSquare y := by
  apply padic_odd_isSquare_of_norm_sub_lt q.property.2 hx hsq
  have hy : ‖y-x‖<1 := (commonRoot_norm_lt_one_iff hneq).mpr hsmall
  have hn : ‖x‖=1 := by rw [Padic.norm_eq_zpow_neg_valuation hx,hvx]; simp
  simpa only [hn] using hy

#print axioms rationalSign_eq_oddSign
#print axioms oddSign_one_of_left_square
#print axioms square_of_positive_perturbation

end FourCorner.HasseOddSymbol
