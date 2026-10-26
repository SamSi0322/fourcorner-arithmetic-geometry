import HilbertDyadicFormulaHigh11
namespace FourCorner.HilbertWellDefinedHigh11
open HilbertArithmeticHigh11 HilbertArithmeticHigh11.Atom
open HilbertOddFormulaHigh11

def negOrder : Atom → ℕ
  | negOne => 1
  | _ => 0

def negativeCount (xs : List Atom) : ℕ := (xs.map negOrder).sum

theorem generator_real_formula (x y : Atom) :
    generatorSign x y 0=(-1 : ℤ)^(negOrder x*negOrder y) := by
  have hp0 (p : OddPrime) : (0 : ℕ)≠p.val := Ne.symm p.property.1.ne_zero
  cases x <;> cases y <;> simp [generatorSign,singleSign,negOrder,hp0]

private theorem row_real_formula (x : Atom) (ys : List Atom) :
    rowSign x ys 0=(-1 : ℤ)^(negOrder x*negativeCount ys) := by
  induction ys with
  | nil => simp [rowSign,negativeCount]
  | cons y ys ih =>
    simp only [rowSign,negativeCount,List.map_cons,List.sum_cons]
    rw [generator_real_formula,ih,Nat.mul_add,pow_add]
    rfl

theorem presentation_real_formula (xs ys : List Atom) :
    presentationSign xs ys 0=(-1 : ℤ)^(negativeCount xs*negativeCount ys) := by
  induction xs with
  | nil => simp [presentationSign,negativeCount]
  | cons x xs ih =>
    simp only [presentationSign,negativeCount,List.map_cons,List.sum_cons]
    rw [row_real_formula,ih,Nat.add_mul,pow_add]
    rfl

theorem signed_eval_positive (xs : List Atom) :
    0 < (-1 : ℚ)^(negativeCount xs)*evalPresentation xs := by
  have ha (x : Atom) : 0 < (-1 : ℚ)^(negOrder x)*value x := by
    cases x with
    | negOne => norm_num [value,negOrder]
    | two => norm_num [value,negOrder]
    | prime p => simpa [value,negOrder] using (show (0 : ℚ)<p.val by exact_mod_cast p.property.1.pos)
  induction xs with
  | nil => norm_num [negativeCount,evalPresentation]
  | cons x xs ih =>
    simp only [negativeCount,List.map_cons,List.sum_cons,evalPresentation,List.prod_cons,pow_add]
    change 0 < ((-1 : ℚ)^negOrder x * (-1 : ℚ)^negativeCount xs)*(value x*evalPresentation xs)
    have hh := mul_pos (ha x) ih
    nlinarith only [hh]

theorem negativeCount_even_of_eval_positive (xs : List Atom) (hp : 0<evalPresentation xs) :
    Even (negativeCount xs) := by
  apply (neg_one_pow_eq_one_iff_even (show (-1 : ℚ)≠1 by norm_num)).mp
  have hh := signed_eval_positive xs
  rcases neg_one_pow_eq_or ℚ (negativeCount xs) with h | h
  · exact h
  · rw [h] at hh; nlinarith

theorem square_eval_real_sign (xs ys : List Atom) (s : ℚ) (hs : s≠0)
    (he : evalPresentation xs=s^2) : presentationSign xs ys 0=1 := by
  have heven := negativeCount_even_of_eval_positive xs (he ▸ sq_pos_of_ne_zero hs)
  rw [presentation_real_formula]
  exact (heven.mul_right _).neg_one_pow

/-- A rational square has trivial arithmetic Hilbert sign at every odd prime;
the proof uses the actual rational valuation and an actual integer square unit. -/
theorem square_eval_odd_sign (q : OddPrime) (xs ys : List Atom) (s : ℚ) (hs : s≠0)
    (he : evalPresentation xs=s^2) : presentationSign xs ys q.val=1 := by
  have hv : (order q xs : ℤ)=2*padicValRat q.val s := by
    rw [← order_valuation,he,padicValRat.pow]
    norm_num
  have heven : Even (order q xs) := by rw [Nat.even_iff]; omega
  have hpow : IsSquare ((q.val : ℚ)^(order q xs)) := heven.isSquare_pow _
  have hEval : IsSquare (evalPresentation xs) := by rw [he]; exact IsSquare.sq _
  have hpq : (q.val : ℚ)≠0 := by exact_mod_cast q.property.1.ne_zero
  have hUnit : IsSquare (unit q xs : ℚ) := by
    have hh := hEval.div hpow
    rw [presentation_factorization,mul_div_cancel_left₀ _ (pow_ne_zero _ hpq)] at hh
    exact hh
  have hInt : IsSquare (unit q xs) := Rat.isSquare_intCast_iff.mp hUnit
  have hLeg : legendreSym q.val (unit q xs)=1 :=
    (legendreSym.eq_one_iff q.val (unit_residue_nonzero q xs)).mpr (hInt.map (Int.castRingHom _))
  rw [presentation_odd_formula]
  simp only [formula,hLeg,one_pow,mul_one]
  have hfirst : (-1 : ℤ)^(order q xs*order q ys*(q.val/2))=1 :=
    ((heven.mul_right _).mul_right _).neg_one_pow
  rw [hfirst,one_mul]
  obtain ⟨k,hk⟩ := heven
  rw [hk,pow_add,← pow_two]
  rw [← pow_mul,Nat.mul_comm _ 2,pow_mul,
    legendreSym.sq_one q.val (unit_residue_nonzero q ys),one_pow]

theorem listSupport_prime (xs : List Atom) {v : ℕ} (hv : v∈listSupport xs) : v.Prime := by
  induction xs with
  | nil => simpa [listSupport] using hv
  | cons x xs ih =>
    simp only [listSupport,Finset.mem_union] at hv
    rcases hv with hx | hxs
    · cases x with
      | negOne => simp [primeSupport] at hx
      | two => simp [primeSupport] at hx
      | prime p =>
        have he : v=p.val := by simpa [primeSupport] using hx
        exact he ▸ p.property.1
    · exact ih hxs

/-- Every rational square has trivial sign at every place. The dyadic case
is forced by the proved global product after proving all the other cases. -/
theorem square_eval_sign (xs ys : List Atom) (s : ℚ) (hs : s≠0)
    (he : evalPresentation xs=s^2) (v : ℕ) : presentationSign xs ys v=1 := by
  have hodd (q : OddPrime) := square_eval_odd_sign q xs ys s hs he
  have hreal := square_eval_real_sign xs ys s hs he
  by_cases hv0 : v=0
  · exact hv0 ▸ hreal
  by_cases hv2 : v=2
  · subst v
    let S := {0,2} ∪ listSupport xs ∪ listSupport ys
    have hprod : (∏ w ∈ S,presentationSign xs ys w)=1 := by
      apply presentation_reciprocity
      · simp [S]
      · simp [S]
      · intro w hw; simp [S,hw]
      · intro w hw; simp [S,hw]
    have hextract : (∏ w ∈ S,presentationSign xs ys w)=presentationSign xs ys 2 := by
      apply Finset.prod_eq_single 2
      · intro w hw hw2
        by_cases hw0 : w=0
        · exact hw0 ▸ hreal
        have hp : w.Prime := by
          simp only [S,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hw
          rcases hw with (h|h)|h
          · rcases h with h|h <;> contradiction
          · exact listSupport_prime xs h
          · exact listSupport_prime ys h
        exact hodd ⟨w,hp,hw2⟩
      · simp [S]
    exact hextract.symm.trans hprod
  by_cases hmem : v∈listSupport xs ∪ listSupport ys
  · have hp : v.Prime := (Finset.mem_union.mp hmem).elim (listSupport_prime xs) (listSupport_prime ys)
    exact hodd ⟨v,hp,hv2⟩
  · simp only [Finset.mem_union,not_or] at hmem
    exact presentationSign_one_outside xs ys v hv0 hv2 hmem.1 hmem.2

theorem generatorSign_symm (x y : Atom) (v : ℕ) : generatorSign x y v=generatorSign y x v := by
  cases x <;> cases y <;> try rfl
  rename_i p q
  by_cases h : p=q
  · subst q; rfl
  · simp [generatorSign,h,Ne.symm h,Nat.mul_comm,mul_comm,mul_left_comm,mul_assoc]

theorem rowSign_append (x : Atom) (ys zs : List Atom) (v : ℕ) :
    rowSign x (ys++zs) v=rowSign x ys v*rowSign x zs v := by
  induction ys with
  | nil => simp [rowSign]
  | cons y ys ih => simp only [List.cons_append,rowSign,ih]; ring

theorem presentationSign_append_left (xs zs ys : List Atom) (v : ℕ) :
    presentationSign (xs++zs) ys v=presentationSign xs ys v*presentationSign zs ys v := by
  induction xs with
  | nil => simp [presentationSign]
  | cons x xs ih => simp only [List.cons_append,presentationSign,ih]; ring

private theorem presentationSign_cons_right (xs : List Atom) (y : Atom) (ys : List Atom) (v : ℕ) :
    presentationSign xs (y::ys) v=rowSign y xs v*presentationSign xs ys v := by
  induction xs with
  | nil => simp [presentationSign,rowSign]
  | cons x xs ih => simp only [presentationSign,rowSign,ih,generatorSign_symm x y v]; ring

theorem presentationSign_symm (xs ys : List Atom) (v : ℕ) :
    presentationSign xs ys v=presentationSign ys xs v := by
  induction xs with
  | nil =>
    have hh : presentationSign ys [] v=1 := by
      induction ys with
      | nil => rfl
      | cons y ys ih => simp [presentationSign,rowSign,ih]
    simp [presentationSign,hh]
  | cons x xs ih => rw [presentationSign,ih,presentationSign_cons_right]

theorem presentationSign_append_right (xs ys zs : List Atom) (v : ℕ) :
    presentationSign xs (ys++zs) v=presentationSign xs ys v*presentationSign xs zs v := by
  rw [presentationSign_symm,presentationSign_append_left,presentationSign_symm ys xs,
    presentationSign_symm zs xs]

@[simp] theorem evalPresentation_append (xs ys : List Atom) :
    evalPresentation (xs++ys)=evalPresentation xs*evalPresentation ys := by
  simp [evalPresentation]

/-- Full independence from the rational square factor and from every choice
of prime factorization, at every place, including the dyadic place. -/
theorem presentation_independent_left (r : ℚ) (hr : r≠0) (xs xs' ys : List Atom)
    (s t : ℚ) (hs : s≠0) (ht : t≠0)
    (hx : r=evalPresentation xs*s^2) (hx' : r=evalPresentation xs'*t^2) (v : ℕ) :
    presentationSign xs ys v=presentationSign xs' ys v := by
  have hs2 := pow_ne_zero 2 hs
  have ht2 := pow_ne_zero 2 ht
  have hxv : evalPresentation xs=r/s^2 := by rw [hx]; field_simp
  have hxv' : evalPresentation xs'=r/t^2 := by rw [hx']; field_simp
  have he : evalPresentation (xs++xs')=(r/(s*t))^2 := by
    rw [evalPresentation_append,hxv,hxv']
    field_simp
    <;> ring
  have hh := square_eval_sign (xs++xs') ys (r/(s*t))
    (div_ne_zero hr (mul_ne_zero hs ht)) he v
  rw [presentationSign_append_left] at hh
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hh with ⟨h1,h2⟩|⟨h1,h2⟩ <;> rw [h1,h2]

theorem presentation_independent_right (r : ℚ) (hr : r≠0) (xs ys ys' : List Atom)
    (s t : ℚ) (hs : s≠0) (ht : t≠0)
    (hy : r=evalPresentation ys*s^2) (hy' : r=evalPresentation ys'*t^2) (v : ℕ) :
    presentationSign xs ys v=presentationSign xs ys' v := by
  rw [presentationSign_symm xs ys,presentationSign_symm xs ys']
  exact presentation_independent_left r hr ys ys' xs s t hs ht hy hy' v

noncomputable def primePresentation (r : ℚ) (hr : r≠0) : List Atom :=
  (rational_presentation r hr).choose
noncomputable def squareScale (r : ℚ) (hr : r≠0) : ℚ :=
  (rational_presentation r hr).choose_spec.choose

theorem squareScale_spec (r : ℚ) (hr : r≠0) :
    squareScale r hr≠0 ∧ r=evalPresentation (primePresentation r hr)*(squareScale r hr)^2 :=
  (rational_presentation r hr).choose_spec.choose_spec

/-- A well-defined rational arithmetic Hilbert sign. Its local formulas and
global product were proved above from prime factorization and quadratic
reciprocity. No quaternion class or evaluation map is postulated. -/
noncomputable def rationalSign (a b : ℚ) (ha : a≠0) (hb : b≠0) (v : ℕ) : ℤ :=
  presentationSign (primePresentation a ha) (primePresentation b hb) v

theorem rationalSign_eq_presentation (a b : ℚ) (ha : a≠0) (hb : b≠0)
    (xs ys : List Atom) (s t : ℚ) (hs : s≠0) (ht : t≠0)
    (hx : a=evalPresentation xs*s^2) (hy : b=evalPresentation ys*t^2) (v : ℕ) :
    rationalSign a b ha hb v=presentationSign xs ys v := by
  unfold rationalSign
  rw [presentation_independent_left a ha _ xs _ (squareScale a ha) s
    (squareScale_spec a ha).1 hs (squareScale_spec a ha).2 hx]
  exact presentation_independent_right b hb xs _ ys (squareScale b hb) t
    (squareScale_spec b hb).1 ht (squareScale_spec b hb).2 hy v

/-- Explicit Hilbert reciprocity for every pair of actual nonzero rational
numbers, with a proved finite support. -/
theorem rational_reciprocity (a b : ℚ) (ha : a≠0) (hb : b≠0) :
    ∃ S : Finset ℕ, 0∈S ∧ 2∈S ∧
      (∏ v ∈ S,rationalSign a b ha hb v)=1 ∧
      (∀ v, v∉S → rationalSign a b ha hb v=1) := by
  let xs := primePresentation a ha
  let ys := primePresentation b hb
  let S := {0,2} ∪ listSupport xs ∪ listSupport ys
  refine ⟨S,by simp [S],by simp [S],?_,?_⟩
  · apply presentation_reciprocity
    · simp [S]
    · simp [S]
    · intro v hv; simp [S,xs,ys,hv]
    · intro v hv; simp [S,xs,ys,hv]
  · intro v hv
    simp only [S,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hv
    exact presentationSign_one_outside xs ys v hv.1.1.1 hv.1.1.2 hv.1.2 hv.2

#print axioms presentation_real_formula
#print axioms square_eval_odd_sign
#print axioms square_eval_sign
#print axioms presentation_independent_left
#print axioms rationalSign_eq_presentation
#print axioms rational_reciprocity
end FourCorner.HilbertWellDefinedHigh11
