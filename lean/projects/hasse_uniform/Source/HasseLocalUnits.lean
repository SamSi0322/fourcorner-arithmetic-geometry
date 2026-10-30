import HasseHilbertArithmetic

/-! Actual normalized units and residue classes in each completed field Q_q.
Negative valuation depths are retained by integer powers of q. -/
namespace FourCorner.HasseLocalUnits

noncomputable section

variable {q : ℕ} [Fact q.Prime]

def unitPart (x : ℚ_[q]) : ℚ_[q] := x*(q : ℚ_[q])^(-x.valuation)

theorem unitPart_ne_zero (x : ℚ_[q]) (hx : x ≠ 0) : unitPart x ≠ 0 := by
  exact mul_ne_zero hx (zpow_ne_zero _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero))

theorem unitPart_valuation (x : ℚ_[q]) (hx : x ≠ 0) : (unitPart x).valuation=0 := by
  rw [unitPart,Padic.valuation_mul hx (zpow_ne_zero _
    (by exact_mod_cast (Fact.out : q.Prime).ne_zero)),Padic.valuation_zpow,Padic.valuation_p]
  ring

theorem unitPart_norm (x : ℚ_[q]) (hx : x ≠ 0) : ‖unitPart x‖=1 := by
  rw [Padic.norm_eq_zpow_neg_valuation (unitPart_ne_zero x hx),unitPart_valuation x hx]
  simp

def normalizedUnit (x : ℚ_[q]) (hx : x ≠ 0) : ℤ_[q]ˣ := PadicInt.mkUnits (unitPart_norm x hx)

@[simp] theorem coe_normalizedUnit (x : ℚ_[q]) (hx : x ≠ 0) :
    ((normalizedUnit x hx : ℤ_[q]) : ℚ_[q])=unitPart x := rfl

theorem unitPart_mul (x y : ℚ_[q]) (hx : x ≠ 0) (hy : y ≠ 0) :
    unitPart (x*y)=unitPart x*unitPart y := by
  rw [unitPart,Padic.valuation_mul hx hy,neg_add,zpow_add₀
    (by exact_mod_cast (Fact.out : q.Prime).ne_zero)]
  dsimp [unitPart]
  ring

theorem normalizedUnit_mul (x y : ℚ_[q]) (hx : x ≠ 0) (hy : y ≠ 0) :
    normalizedUnit (x*y) (mul_ne_zero hx hy)=normalizedUnit x hx*normalizedUnit y hy := by
  apply Units.ext
  apply Subtype.ext
  exact unitPart_mul x y hx hy

def residueUnit (x : ℚ_[q]) (hx : x ≠ 0) : (ZMod q)ˣ :=
  Units.map (PadicInt.toZMod : ℤ_[q] →+* ZMod q).toMonoidHom (normalizedUnit x hx)

def residue (x : ℚ_[q]) (hx : x ≠ 0) : ZMod q := residueUnit x hx

theorem residue_ne_zero (x : ℚ_[q]) (hx : x ≠ 0) : residue x hx ≠ 0 := Units.ne_zero _

theorem residue_mul (x y : ℚ_[q]) (hx : x ≠ 0) (hy : y ≠ 0) :
    residue (x*y) (mul_ne_zero hx hy)=residue x hx*residue y hy := by
  change PadicInt.toZMod (normalizedUnit (x*y) (mul_ne_zero hx hy) : ℤ_[q])=
    PadicInt.toZMod (normalizedUnit x hx : ℤ_[q])*PadicInt.toZMod (normalizedUnit y hy : ℤ_[q])
  rw [normalizedUnit_mul x y hx hy,Units.val_mul,map_mul]

theorem residue_sq (x : ℚ_[q]) (hx : x ≠ 0) :
    residue (x^2) (pow_ne_zero _ hx)=(residue x hx)^2 := by
  simpa only [pow_two] using residue_mul x x hx hx

theorem unitPart_qpow (k : ℤ) : unitPart ((q : ℚ_[q])^k)=1 := by
  have hq : (q : ℚ_[q]) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  simp only [unitPart,Padic.valuation_zpow,Padic.valuation_p,mul_one]
  rw [← zpow_add₀ hq]
  simp

theorem residue_eq_one_of_unitPart_eq_one (x : ℚ_[q]) (hx : x ≠ 0)
    (h : unitPart x=1) : residue x hx=1 := by
  have hu : normalizedUnit x hx=1 := by
    apply Units.ext
    apply Subtype.ext
    exact h
  simp only [residue,residueUnit,hu,map_one,Units.val_one]

theorem residue_qpow (k : ℤ) : residue ((q : ℚ_[q])^k)
    (zpow_ne_zero k (by exact_mod_cast (Fact.out : q.Prime).ne_zero))=1 :=
  residue_eq_one_of_unitPart_eq_one _ _ (unitPart_qpow k)

/-- Literal integer units have their literal residue in the actual local
residue field; this connects completion arithmetic to finite-field characters. -/
theorem residue_intCast (n : ℤ) (hn : (n : ZMod q) ≠ 0) :
    residue (n : ℚ_[q]) (by
      intro hh
      have hn0 : n=0 := by exact_mod_cast hh
      exact hn (by simp [hn0]))=(n : ZMod q) := by
  have hn0 : n ≠ 0 := by intro hh; exact hn (by simp [hh])
  have hv : (n : ℚ_[q]).valuation=0 := by
    rw [Padic.valuation_intCast]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd (fun hd => hn
      ((ZMod.intCast_zmod_eq_zero_iff_dvd n q).mpr hd))
  have hu : (normalizedUnit (n : ℚ_[q]) (by exact_mod_cast hn0) : ℤ_[q])=(n : ℤ_[q]) := by
    apply Subtype.ext
    simp only [coe_normalizedUnit,unitPart,hv,neg_zero,zpow_zero,mul_one]
    rfl
  change PadicInt.toZMod (normalizedUnit (n : ℚ_[q]) _)=(n : ZMod q)
  rw [hu,map_intCast]

/-- The unit of a signed prime presentation is the actual completion unit,
after removing the literal q-power, not an unrelated character label. -/
theorem residue_evalPresentation (q : HilbertArithmeticHigh11.OddPrime)
    (xs : List HilbertArithmeticHigh11.Atom) :
    residue (HilbertArithmeticHigh11.evalPresentation xs : ℚ_[q.val])
      (by exact_mod_cast HilbertOddFormulaHigh11.evalPresentation_ne_zero xs) =
      (HilbertOddFormulaHigh11.unit q xs : ZMod q.val) := by
  have hp : (q.val : ℚ_[q.val]) ≠ 0 := by exact_mod_cast q.property.1.ne_zero
  have hu : (HilbertOddFormulaHigh11.unit q xs : ℚ_[q.val]) ≠ 0 := by
    exact_mod_cast HilbertOddFormulaHigh11.unit_ne_zero q xs
  have he : (HilbertArithmeticHigh11.evalPresentation xs : ℚ_[q.val])=
      (q.val : ℚ_[q.val])^(HilbertOddFormulaHigh11.order q xs)*
        (HilbertOddFormulaHigh11.unit q xs : ℚ_[q.val]) := by
    exact_mod_cast HilbertOddFormulaHigh11.presentation_factorization q xs
  have hh := residue_mul ((q.val : ℚ_[q.val])^(HilbertOddFormulaHigh11.order q xs))
    (HilbertOddFormulaHigh11.unit q xs : ℚ_[q.val]) (pow_ne_zero _ hp) hu
  have hpow : residue ((q.val : ℚ_[q.val])^(HilbertOddFormulaHigh11.order q xs))
      (pow_ne_zero _ hp)=1 := by
    simpa only [zpow_natCast] using residue_qpow (q:=q.val) (HilbertOddFormulaHigh11.order q xs : ℤ)
  rw [hpow,residue_intCast _ (HilbertOddFormulaHigh11.unit_residue_nonzero q xs),one_mul] at hh
  simpa only [← he] using hh

/-- Every rational square scale contributes a literal nonzero square to the
actual normalized residue, including when its valuation is negative. -/
theorem rational_residue_presentation (q : HilbertArithmeticHigh11.OddPrime)
    (xs : List HilbertArithmeticHigh11.Atom) (s r : ℚ) (hs : s ≠ 0)
    (hr : r=HilbertArithmeticHigh11.evalPresentation xs*s^2) :
    ∃ (hr0 : (r : ℚ_[q.val]) ≠ 0) (t : ZMod q.val), t ≠ 0 ∧
      residue (r : ℚ_[q.val]) hr0=(HilbertOddFormulaHigh11.unit q xs : ZMod q.val)*t^2 := by
  have hs0 : (s : ℚ_[q.val]) ≠ 0 := by exact_mod_cast hs
  have he0 : (HilbertArithmeticHigh11.evalPresentation xs : ℚ_[q.val]) ≠ 0 := by
    exact_mod_cast HilbertOddFormulaHigh11.evalPresentation_ne_zero xs
  have hr0 : (r : ℚ_[q.val]) ≠ 0 := by
    have hh : r ≠ 0 := by
      rw [hr]
      exact mul_ne_zero (HilbertOddFormulaHigh11.evalPresentation_ne_zero xs) (pow_ne_zero _ hs)
    exact_mod_cast hh
  refine ⟨hr0,residue (s : ℚ_[q.val]) hs0,residue_ne_zero _ hs0,?_⟩
  have he : (r : ℚ_[q.val])=(HilbertArithmeticHigh11.evalPresentation xs : ℚ_[q.val])*(s : ℚ_[q.val])^2 := by
    exact_mod_cast hr
  have hh := residue_mul (HilbertArithmeticHigh11.evalPresentation xs : ℚ_[q.val])
    ((s : ℚ_[q.val])^2) he0 (pow_ne_zero _ hs0)
  rw [residue_evalPresentation,residue_sq] at hh
  simpa only [← he] using hh

/-- Exact character compatibility between high11's integer unit formula and
the residue of the corresponding rational in its actual completed field. -/
theorem quadraticChar_rational_residue (q : HilbertArithmeticHigh11.OddPrime)
    (xs : List HilbertArithmeticHigh11.Atom) (s r : ℚ) (hs : s ≠ 0)
    (hr : r=HilbertArithmeticHigh11.evalPresentation xs*s^2) (hr0 : (r : ℚ_[q.val]) ≠ 0) :
    quadraticChar (ZMod q.val) (residue (r : ℚ_[q.val]) hr0)=
      legendreSym q.val (HilbertOddFormulaHigh11.unit q xs) := by
  obtain ⟨hr0',t,ht,he⟩ := rational_residue_presentation q xs s r hs hr
  rw [he,map_mul,quadraticChar_sq_one' ht,mul_one]
  rfl

#print axioms unitPart_valuation
#print axioms normalizedUnit_mul
#print axioms residue_ne_zero
#print axioms residue_mul
#print axioms residue_sq
#print axioms residue_qpow
#print axioms residue_intCast
#print axioms residue_evalPresentation
#print axioms rational_residue_presentation
#print axioms quadraticChar_rational_residue

end
end FourCorner.HasseLocalUnits
