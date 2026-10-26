import HilbertOddFormulaHigh11
namespace FourCorner.HilbertDyadicFormulaHigh11
open HilbertArithmeticHigh11 HilbertArithmeticHigh11.Atom

/-- The literal exponent in the dyadic Hilbert rule, read on unit residues
modulo eight and valuation parities modulo two. -/
def formula (r : ZMod 2) (u : ZMod 8) (s : ZMod 2) (v : ZMod 8) : ℤ :=
  (-1)^(((u.val-1)/2)*((v.val-1)/2)+r.val*((v.val^2-1)/8)+s.val*((u.val^2-1)/8))

def OddUnit (u : ZMod 8) : Prop := u.val % 2=1
instance (u : ZMod 8) : Decidable (OddUnit u) := inferInstanceAs (Decidable (u.val%2=1))

set_option maxRecDepth 100000 in
private theorem finite_mul_left : ∀ (r r' s : ZMod 2) (u u' v : ZMod 8),
    OddUnit u → OddUnit u' → OddUnit v →
    formula (r+r') (u*u') s v=formula r u s v*formula r' u' s v := by decide

set_option maxRecDepth 100000 in
private theorem finite_mul_right : ∀ (r s s' : ZMod 2) (u v v' : ZMod 8),
    OddUnit u → OddUnit v → OddUnit v' →
    formula r u (s+s') (v*v')=formula r u s v*formula r u s' v' := by decide

private theorem finite_odd_mul : ∀ u v : ZMod 8, OddUnit u → OddUnit v → OddUnit (u*v) := by decide
private theorem finite_one_right : ∀ (r : ZMod 2) (u : ZMod 8), formula r u 0 1=1 := by decide
private theorem finite_one_left : ∀ (s : ZMod 2) (v : ZMod 8), formula 0 1 s v=1 := by decide

/-- Exact finite character identities for the two supplementary laws. -/
private theorem chi8_formula : ∀ u : ZMod 8, OddUnit u →
    ZMod.χ₈ u = (-1 : ℤ)^((u.val^2-1)/8) := by decide

private theorem oddPrime_residue (p : OddPrime) : OddUnit (p.val : ZMod 8) := by
  have h := (Nat.Prime.mod_two_eq_one_iff_ne_two p.property.1).mpr p.property.2
  change p.val%8%2=1
  omega

private theorem minus_one_exponent (p : OddPrime) :
    (legendreSym p.val (-1))=(-1 : ℤ)^((((p.val : ZMod 8).val)-1)/2) := by
  rw [legendreSym.at_neg_one p.property.2,
    ZMod.χ₄_eq_neg_one_pow ((Nat.Prime.mod_two_eq_one_iff_ne_two p.property.1).mpr p.property.2)]
  have hm : p.val/2%2=(p.val%8-1)/2%2 := by
    have h := (Nat.Prime.mod_two_eq_one_iff_ne_two p.property.1).mpr p.property.2
    omega
  rw [neg_one_pow_eq_pow_mod_two,neg_one_pow_eq_pow_mod_two (((p.val : ZMod 8).val-1)/2)]
  congr 1

private theorem two_exponent (p : OddPrime) :
    legendreSym p.val 2=(-1 : ℤ)^((((p.val : ZMod 8).val)^2-1)/8) := by
  rw [legendreSym.at_two p.property.2]
  exact chi8_formula _ (oddPrime_residue p)

def atomOrder : Atom → ℕ
  | two => 1
  | _ => 0

def atomUnit : Atom → ℤ
  | negOne => -1
  | two => 1
  | prime p => p.val

def order (xs : List Atom) : ℕ := (xs.map atomOrder).sum
def unit (xs : List Atom) : ℤ := (xs.map atomUnit).prod

private theorem atom_odd_residue (x : Atom) : OddUnit (atomUnit x : ZMod 8) := by
  cases x with
  | negOne => decide
  | two => decide
  | prime p => simpa [atomUnit] using oddPrime_residue p

private theorem finite_neg_left : ∀ u : ZMod 8,
    formula 0 (-1) 0 u=(-1 : ℤ)^((u.val-1)/2) := by decide
private theorem finite_neg_right : ∀ u : ZMod 8,
    formula 0 u 0 (-1)=(-1 : ℤ)^((u.val-1)/2) := by decide
private theorem finite_two_left : ∀ u : ZMod 8,
    formula 1 1 0 u=(-1 : ℤ)^((u.val^2-1)/8) := by decide
private theorem finite_two_right : ∀ u : ZMod 8,
    formula 0 u 1 1=(-1 : ℤ)^((u.val^2-1)/8) := by decide

private theorem odd_pair_exponent (p q : OddPrime) :
    (-1 : ℤ)^(p.val/2*(q.val/2)) =
      (-1 : ℤ)^((((p.val : ZMod 8).val-1)/2)*(((q.val : ZMod 8).val-1)/2)) := by
  have hp : p.val/2%2=(p.val%8-1)/2%2 := by
    have h := (Nat.Prime.mod_two_eq_one_iff_ne_two p.property.1).mpr p.property.2; omega
  have hq : q.val/2%2=(q.val%8-1)/2%2 := by
    have h := (Nat.Prime.mod_two_eq_one_iff_ne_two q.property.1).mpr q.property.2; omega
  rw [neg_one_pow_eq_pow_mod_two,
    neg_one_pow_eq_pow_mod_two ((((p.val : ZMod 8).val-1)/2)*(((q.val : ZMod 8).val-1)/2))]
  congr 1
  change (p.val/2*(q.val/2))%2 = ((p.val%8-1)/2*((q.val%8-1)/2))%2
  calc
    _ = (p.val/2%2)*(q.val/2%2)%2 := Nat.mul_mod _ _ _
    _ = ((p.val%8-1)/2%2)*((q.val%8-1)/2%2)%2 := by rw [hp,hq]
    _ = _ := (Nat.mul_mod _ _ _).symm

/-- The exact standard dyadic formula on every signed prime generator pair. -/
theorem generator_dyadic_formula (x y : Atom) :
    generatorSign x y 2=formula (atomOrder x : ZMod 2) (atomUnit x : ZMod 8)
      (atomOrder y : ZMod 2) (atomUnit y : ZMod 8) := by
  cases x <;> cases y
  · decide
  · decide
  · rename_i p
    simp only [generatorSign,singleSign,ite_true,
      if_neg (Ne.symm p.property.2),mul_one,atomOrder,atomUnit,Int.cast_neg,Int.cast_one,
      Int.cast_natCast,Nat.cast_zero]
    rw [finite_neg_left,minus_one_exponent]
  · decide
  · decide
  · rename_i p
    simp only [generatorSign,singleSign,ite_true,
      if_neg (Ne.symm p.property.2),mul_one,atomOrder,atomUnit,Int.cast_one,Int.cast_natCast,
      Nat.cast_zero,Nat.cast_one]
    rw [finite_two_left,two_exponent]
  · rename_i p
    simp only [generatorSign,singleSign,ite_true,
      if_neg (Ne.symm p.property.2),mul_one,atomOrder,atomUnit,Int.cast_neg,Int.cast_one,
      Int.cast_natCast,Nat.cast_zero]
    rw [finite_neg_right,minus_one_exponent]
  · rename_i p
    simp only [generatorSign,singleSign,ite_true,
      if_neg (Ne.symm p.property.2),mul_one,atomOrder,atomUnit,Int.cast_one,Int.cast_natCast,
      Nat.cast_zero,Nat.cast_one]
    rw [finite_two_right,two_exponent]
  · rename_i p q
    by_cases hpq : p=q
    · subst q
      simp only [generatorSign,ite_true,singleSign,
        if_neg (Ne.symm p.property.2),mul_one]
      rw [minus_one_exponent]
      simp only [atomOrder,atomUnit,Nat.cast_zero,Int.cast_natCast,formula,ZMod.val_zero,
        zero_mul,add_zero]
      have hh : ∀ u : ZMod 8,
          ((-1 : ℤ)^((u.val-1)/2))=(-1)^(((u.val-1)/2)*((u.val-1)/2)) := by decide
      exact hh _
    · simp only [generatorSign,if_neg hpq,singleSign,ite_true,
        if_neg (Ne.symm p.property.2),if_neg (Ne.symm q.property.2),mul_one,
        atomOrder,atomUnit,Nat.cast_zero,Int.cast_natCast,formula,ZMod.val_zero,
        zero_mul,add_zero]
      exact odd_pair_exponent p q

private theorem unit_odd_residue (xs : List Atom) : OddUnit (unit xs : ZMod 8) := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    simpa only [unit,List.map_cons,List.prod_cons,Int.cast_mul] using
      finite_odd_mul _ _ (atom_odd_residue x) ih

private theorem row_dyadic_formula (x : Atom) (ys : List Atom) :
    rowSign x ys 2=formula (atomOrder x : ZMod 2) (atomUnit x : ZMod 8)
      (order ys : ZMod 2) (unit ys : ZMod 8) := by
  induction ys with
  | nil => exact (finite_one_right _ _).symm
  | cons y ys ih =>
    simp only [rowSign,order,unit,List.map_cons,List.sum_cons,List.prod_cons,Nat.cast_add,Int.cast_mul]
    rw [generator_dyadic_formula,ih,← finite_mul_right _ _ _ _ _ _
      (atom_odd_residue x) (atom_odd_residue y) (unit_odd_residue ys)]
    rfl

/-- The complete dyadic Hilbert rule for every finite signed prime
presentation, obtained from the actual unit residues and valuation parities. -/
theorem presentation_dyadic_formula (xs ys : List Atom) :
    presentationSign xs ys 2=formula (order xs : ZMod 2) (unit xs : ZMod 8)
      (order ys : ZMod 2) (unit ys : ZMod 8) := by
  induction xs with
  | nil => exact (finite_one_left _ _).symm
  | cons x xs ih =>
    simp only [presentationSign,order,unit,List.map_cons,List.sum_cons,List.prod_cons,Nat.cast_add,Int.cast_mul]
    rw [row_dyadic_formula,ih,← finite_mul_left _ _ _ _ _ _
      (atom_odd_residue x) (unit_odd_residue xs) (unit_odd_residue ys)]
    rfl

theorem presentation_factorization (xs : List Atom) :
    evalPresentation xs=(2 : ℚ)^(order xs)*(unit xs : ℚ) := by
  have ha (x : Atom) : value x=(2 : ℚ)^(atomOrder x)*(atomUnit x : ℚ) := by
    cases x <;> simp [value,atomOrder,atomUnit]
  induction xs with
  | nil => simp [evalPresentation,order,unit]
  | cons x xs ih =>
    simp only [evalPresentation,List.map_cons,List.prod_cons]
    change value x*evalPresentation xs=_
    rw [ha,ih]
    simp only [order,unit,List.map_cons,List.sum_cons,List.prod_cons,Int.cast_mul,pow_add]
    ring

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem unit_residue_nonzero (xs : List Atom) : (unit xs : ZMod 2)≠0 := by
  have hh : ∀ u : ZMod 8, OddUnit u →
      (ZMod.castHom (by decide : 2∣8) (ZMod 2)) u ≠ 0 := by decide
  simpa only [map_intCast] using hh (unit xs) (unit_odd_residue xs)

theorem unit_valuation (xs : List Atom) : padicValRat 2 (unit xs : ℚ)=0 := by
  rw [padicValRat.of_int]
  have hh := padicValInt.eq_zero_of_not_dvd (fun hd => unit_residue_nonzero xs
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd))
  exact_mod_cast hh

/-- The dyadic exponent used in the explicit residue formula is the actual
valuation of the literal signed prime presentation. -/
theorem order_valuation (xs : List Atom) : padicValRat 2 (evalPresentation xs)=(order xs : ℤ) := by
  rw [presentation_factorization]
  have hu : (unit xs : ℚ)≠0 := by
    have hh : unit xs≠0 := fun h => unit_residue_nonzero xs (by rw [h]; simp)
    exact_mod_cast hh
  rw [padicValRat.mul (by norm_num) hu,padicValRat.pow,
    show padicValRat 2 (2 : ℚ)=1 by simpa using padicValRat.self (by norm_num : 1<2),unit_valuation]
  simp

theorem rational_presentation_valuation (xs : List Atom) (s r : ℚ)
    (hs : s≠0) (hr : r=evalPresentation xs*s^2) :
    padicValRat 2 r=(order xs : ℤ)+2*padicValRat 2 s := by
  rw [hr,padicValRat.mul (HilbertOddFormulaHigh11.evalPresentation_ne_zero xs) (pow_ne_zero _ hs),
    order_valuation,padicValRat.pow]
  norm_num

#print axioms generator_dyadic_formula
#print axioms presentation_dyadic_formula
#print axioms presentation_factorization
#print axioms order_valuation
#print axioms rational_presentation_valuation
end FourCorner.HilbertDyadicFormulaHigh11
