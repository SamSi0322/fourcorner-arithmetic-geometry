import HasseOddSymbol
import HasseTangentGlobal

set_option maxHeartbeats 1000000
namespace FourCorner.HasseDyadicSymbol
open HilbertArithmeticHigh11 HilbertWellDefinedHigh11 HasseLocalUnits

noncomputable section

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The actual mod-eight residue of the normalized unit in Q₂. -/
def residue8 (x : ℚ_[2]) (hx : x ≠ 0) : ZMod 8 :=
  PadicInt.toZModPow 3 (normalizedUnit x hx : ℤ_[2])

theorem residue8_odd (x : ℚ_[2]) (hx : x ≠ 0) :
    HilbertDyadicFormulaHigh11.OddUnit (residue8 x hx) := by
  have hn : (ZMod.castHom (by decide : 2∣8) (ZMod 2)) (residue8 x hx) ≠ 0 := by
    have hu : ‖(normalizedUnit x hx : ℤ_[2])‖=1 := unitPart_norm x hx
    have hr := (dyadic_norm_one_iff_residue_ne_zero _).mp hu
    have hc := PadicInt.cast_toZModPow (p:=2) 1 3 (by decide) (normalizedUnit x hx : ℤ_[2])
    simpa only [residue8,ZMod.castHom_apply,hc] using hr
  have hf : ∀ u : ZMod 8,
      (ZMod.castHom (by decide : 2∣8) (ZMod 2)) u ≠ 0 →
      HilbertDyadicFormulaHigh11.OddUnit u := by decide
  exact hf _ hn

theorem residue8_mul (x y : ℚ_[2]) (hx : x ≠ 0) (hy : y ≠ 0) :
    residue8 (x*y) (mul_ne_zero hx hy)=residue8 x hx*residue8 y hy := by
  unfold residue8
  rw [normalizedUnit_mul x y hx hy,Units.val_mul,map_mul]

theorem residue8_sq (x : ℚ_[2]) (hx : x ≠ 0) :
    residue8 (x^2) (pow_ne_zero _ hx)=1 := by
  have hf : ∀ u : ZMod 8, HilbertDyadicFormulaHigh11.OddUnit u → u*u=1 := by decide
  simpa only [pow_two] using (residue8_mul x x hx hx).trans (hf _ (residue8_odd x hx))

theorem residue8_qpow (k : ℤ) : residue8 ((2 : ℚ_[2])^k)
    (zpow_ne_zero k (by norm_num))=1 := by
  have hu : normalizedUnit ((2 : ℚ_[2])^k) (zpow_ne_zero k (by norm_num))=1 := by
    apply Units.ext
    apply Subtype.ext
    exact unitPart_qpow (q:=2) k
  simp only [residue8,hu,Units.val_one,map_one]

/-- Literal integer units have their literal residue at every power. -/
theorem normalizedUnit_intCast {q : ℕ} [Fact q.Prime] (n : ℤ) (hn : (n : ZMod q) ≠ 0) :
    (normalizedUnit (n : ℚ_[q]) (by
      intro hh
      have hn0 : n=0 := by exact_mod_cast hh
      exact hn (by simp [hn0])) : ℤ_[q])=(n : ℤ_[q]) := by
  have hn0 : n ≠ 0 := by intro hh; exact hn (by simp [hh])
  have hv : (n : ℚ_[q]).valuation=0 := by
    rw [Padic.valuation_intCast]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd (fun hd => hn
      ((ZMod.intCast_zmod_eq_zero_iff_dvd n q).mpr hd))
  apply Subtype.ext
  simp only [coe_normalizedUnit,unitPart,hv,neg_zero,zpow_zero,mul_one]
  rfl

theorem residue8_intCast (n : ℤ) (hn : (n : ZMod 2) ≠ 0) :
    residue8 (n : ℚ_[2]) (by
      intro hh
      have hn0 : n=0 := by exact_mod_cast hh
      exact hn (by simp [hn0]))=(n : ZMod 8) := by
  unfold residue8
  rw [normalizedUnit_intCast n hn,map_intCast]

/-- The signed prime presentation gives the same actual Q₂ unit, modulo 8. -/
theorem residue8_evalPresentation (xs : List Atom) :
    residue8 (evalPresentation xs : ℚ_[2])
      (by exact_mod_cast HilbertOddFormulaHigh11.evalPresentation_ne_zero xs)=
      (HilbertDyadicFormulaHigh11.unit xs : ZMod 8) := by
  have hu : (HilbertDyadicFormulaHigh11.unit xs : ℚ_[2]) ≠ 0 := by
    have hh : HilbertDyadicFormulaHigh11.unit xs ≠ 0 := by
      intro hh
      exact HilbertDyadicFormulaHigh11.unit_residue_nonzero xs (by simp [hh])
    exact_mod_cast hh
  have he : (evalPresentation xs : ℚ_[2])=
      (2 : ℚ_[2])^(HilbertDyadicFormulaHigh11.order xs)*
        (HilbertDyadicFormulaHigh11.unit xs : ℚ_[2]) := by
    exact_mod_cast HilbertDyadicFormulaHigh11.presentation_factorization xs
  have hh := residue8_mul ((2 : ℚ_[2])^(HilbertDyadicFormulaHigh11.order xs))
    (HilbertDyadicFormulaHigh11.unit xs : ℚ_[2]) (pow_ne_zero _ (by norm_num)) hu
  have hpow : residue8 ((2 : ℚ_[2])^(HilbertDyadicFormulaHigh11.order xs))
      (pow_ne_zero _ (by norm_num))=1 := by
    simpa only [zpow_natCast] using residue8_qpow (HilbertDyadicFormulaHigh11.order xs : ℤ)
  rw [hpow,residue8_intCast _ (HilbertDyadicFormulaHigh11.unit_residue_nonzero xs),one_mul] at hh
  simpa only [← he] using hh

/-- Rational square factors, at any positive or negative depth, contribute
one to the normalized mod-eight residue. -/
theorem rational_residue8_presentation (xs : List Atom) (s r : ℚ) (hs : s ≠ 0)
    (hr : r=evalPresentation xs*s^2) (hr0 : (r : ℚ_[2]) ≠ 0) :
    residue8 (r : ℚ_[2]) hr0=(HilbertDyadicFormulaHigh11.unit xs : ZMod 8) := by
  have hs0 : (s : ℚ_[2]) ≠ 0 := by exact_mod_cast hs
  have he0 : (evalPresentation xs : ℚ_[2]) ≠ 0 := by
    exact_mod_cast HilbertOddFormulaHigh11.evalPresentation_ne_zero xs
  have he : (r : ℚ_[2])=(evalPresentation xs : ℚ_[2])*(s : ℚ_[2])^2 := by
    exact_mod_cast hr
  have hh := residue8_mul (evalPresentation xs : ℚ_[2]) ((s : ℚ_[2])^2)
    he0 (pow_ne_zero _ hs0)
  rw [residue8_evalPresentation,residue8_sq _ hs0,mul_one] at hh
  simpa only [← he] using hh

/-- Standard dyadic sign on actual Q₂, using its literal valuation and
normalized unit mod 8. -/
def dyadicSign (x y : ℚ_[2]) (hx : x ≠ 0) (hy : y ≠ 0) : ℤ :=
  HilbertDyadicFormulaHigh11.formula (x.valuation : ZMod 2) (residue8 x hx)
    (y.valuation : ZMod 2) (residue8 y hy)

/-- Genuine completed-field comparison, on the same two rational inputs,
uniform in all valuation depths. -/
theorem rationalSign_eq_dyadicSign (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    rationalSign a b ha hb 2=dyadicSign (a : ℚ_[2]) (b : ℚ_[2])
      (by exact_mod_cast ha) (by exact_mod_cast hb) := by
  let xs := primePresentation a ha
  let ys := primePresentation b hb
  have hvx : ((a : ℚ_[2]).valuation : ZMod 2)=
      (HilbertDyadicFormulaHigh11.order xs : ZMod 2) := by
    rw [Padic.valuation_ratCast,HilbertDyadicFormulaHigh11.rational_presentation_valuation xs
      (squareScale a ha) a (squareScale_spec a ha).1 (squareScale_spec a ha).2]
    push_cast
    simp only [show (2 : ZMod 2)=0 by decide,zero_mul,add_zero]
  have hvy : ((b : ℚ_[2]).valuation : ZMod 2)=
      (HilbertDyadicFormulaHigh11.order ys : ZMod 2) := by
    rw [Padic.valuation_ratCast,HilbertDyadicFormulaHigh11.rational_presentation_valuation ys
      (squareScale b hb) b (squareScale_spec b hb).1 (squareScale_spec b hb).2]
    push_cast
    simp only [show (2 : ZMod 2)=0 by decide,zero_mul,add_zero]
  have hux := rational_residue8_presentation xs (squareScale a ha) a
    (squareScale_spec a ha).1 (squareScale_spec a ha).2 (by exact_mod_cast ha)
  have huy := rational_residue8_presentation ys (squareScale b hb) b
    (squareScale_spec b hb).1 (squareScale_spec b hb).2 (by exact_mod_cast hb)
  change presentationSign xs ys 2=_
  rw [HilbertDyadicFormulaHigh11.presentation_dyadic_formula]
  simp only [dyadicSign,hvx,hvy,hux,huy]

/-- A square first entry is trivial for the actual dyadic sign. -/
theorem dyadicSign_one_of_left_square (x y : ℚ_[2]) (hx : x ≠ 0) (hy : y ≠ 0)
    (hsq : IsSquare x) : dyadicSign x y hx hy=1 := by
  obtain ⟨s,hs⟩ := hsq
  have he : x=s^2 := by simpa only [pow_two] using hs
  have hs0 : s ≠ 0 := by intro hh; apply hx; simp [he,hh]
  have hv : (x.valuation : ZMod 2)=0 := by
    rw [he,Padic.valuation_pow]
    push_cast
    simp only [show (2 : ZMod 2)=0 by decide,zero_mul]
  have hr : residue8 x hx=1 := by simpa only [← he] using residue8_sq s hs0
  have hf : ∀ (s : ZMod 2) (v : ZMod 8),
      HilbertDyadicFormulaHigh11.formula 0 1 s v=1 := by decide
  exact (show dyadicSign x y hx hy=HilbertDyadicFormulaHigh11.formula 0 1
    (y.valuation : ZMod 2) (residue8 y hy) by simp only [dyadicSign,hv,hr]).trans (hf _ _)

theorem dyadicSign_mul_sq_left (x y s : ℚ_[2]) (hx : x ≠ 0) (hy : y ≠ 0)
    (hs : s ≠ 0) :
    dyadicSign (x*s^2) y (mul_ne_zero hx (pow_ne_zero _ hs)) hy=dyadicSign x y hx hy := by
  have hv : ((x*s^2).valuation : ZMod 2)=(x.valuation : ZMod 2) := by
    rw [Padic.valuation_mul hx (pow_ne_zero _ hs),Padic.valuation_pow]
    push_cast
    simp only [show (2 : ZMod 2)=0 by decide,zero_mul,add_zero]
  have hr : residue8 (x*s^2) (mul_ne_zero hx (pow_ne_zero _ hs))=residue8 x hx := by
    rw [residue8_mul _ _ hx (pow_ne_zero _ hs),residue8_sq _ hs,mul_one]
  simp only [dyadicSign,hv,hr]

theorem dyadicSign_mul_sq_right (x y s : ℚ_[2]) (hx : x ≠ 0) (hy : y ≠ 0)
    (hs : s ≠ 0) :
    dyadicSign x (y*s^2) hx (mul_ne_zero hy (pow_ne_zero _ hs))=dyadicSign x y hx hy := by
  have hv : ((y*s^2).valuation : ZMod 2)=(y.valuation : ZMod 2) := by
    rw [Padic.valuation_mul hy (pow_ne_zero _ hs),Padic.valuation_pow]
    push_cast
    simp only [show (2 : ZMod 2)=0 by decide,zero_mul,add_zero]
  have hr : residue8 (y*s^2) (mul_ne_zero hy (pow_ne_zero _ hs))=residue8 y hy := by
    rw [residue8_mul _ _ hy (pow_ne_zero _ hs),residue8_sq _ hs,mul_one]
  simp only [dyadicSign,hv,hr]

theorem residue8_negTwo : residue8 (-2 : ℚ_[2]) (by norm_num)= -1 := by
  have hh := residue8_mul (-1 : ℚ_[2]) 2 (by norm_num) (by norm_num)
  have ht : residue8 (2 : ℚ_[2]) (by norm_num)=1 := by
    simpa using residue8_qpow 1
  have hm : residue8 (-1 : ℚ_[2]) (by norm_num)= -1 := by
    simpa only [Int.cast_neg,Int.cast_one] using residue8_intCast (-1) (by decide)
  rw [hm,ht] at hh
  norm_num at hh ⊢
  exact hh

theorem dyadicSign_negTwo_negTwo :
    dyadicSign (-2 : ℚ_[2]) (-2) (by norm_num) (by norm_num)= -1 := by
  have hv : (-2 : ℚ_[2]).valuation=1 := by
    rw [show (-2 : ℚ_[2])= -(2 : ℚ_[2]) by ring,commonRoot_val_neg]
    exact Padic.valuation_p
  rw [dyadicSign,hv,residue8_negTwo]
  decide

theorem dyadicSign_two_negTwo :
    dyadicSign (2 : ℚ_[2]) (-2) (by norm_num) (by norm_num)=1 := by
  have hv : (-2 : ℚ_[2]).valuation=1 := by
    rw [show (-2 : ℚ_[2])= -(2 : ℚ_[2]) by ring,commonRoot_val_neg]
    exact Padic.valuation_p
  have ht : residue8 (2 : ℚ_[2]) (by norm_num)=1 := by simpa using residue8_qpow 1
  rw [dyadicSign,hv,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,residue8_negTwo,ht]
  decide

theorem dyadicSign_one_left (y : ℚ_[2]) (hy : y ≠ 0) :
    dyadicSign 1 y one_ne_zero hy=1 :=
  dyadicSign_one_of_left_square 1 y one_ne_zero hy IsSquare.one

/-- The original source tangent coefficient itself receives the actual Q₂
sign; no local point or coefficient substitution occurs in this comparison. -/
theorem tangentSign_eq_dyadicSign (p : ℚ) (hp : 1<p)
    (P : HasseRationalSource.HomogeneousPoint p) (D : HasseAnchorChoice.TangentData p P) :
    HasseTangentGlobal.tangentSign p hp P D 2=
      dyadicSign (HasseTangentGlobal.firstCoefficient p : ℚ_[2])
        (HasseTangentGlobal.secondCoefficient p P D : ℚ_[2])
        (by exact_mod_cast (ne_of_lt (HasseTangentGlobal.firstCoefficient_negative p hp)))
        (by exact_mod_cast (ne_of_lt D.coefficient_negative)) := by
  exact rationalSign_eq_dyadicSign _ _ _ _

#print axioms residue8_odd
#print axioms residue8_mul
#print axioms residue8_sq
#print axioms residue8_evalPresentation
#print axioms rational_residue8_presentation
#print axioms rationalSign_eq_dyadicSign
#print axioms dyadicSign_one_of_left_square
#print axioms dyadicSign_mul_sq_left
#print axioms dyadicSign_mul_sq_right
#print axioms dyadicSign_negTwo_negTwo
#print axioms dyadicSign_two_negTwo
#print axioms tangentSign_eq_dyadicSign
end
end FourCorner.HasseDyadicSymbol
