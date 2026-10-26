import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Factors
import FourCorner.RationalSquarefree
import Mathlib.Tactic
/-! Explicit arithmetic reciprocity on signed prime presentations.
The values are the literal Hilbert-sign formulas on the generators -1, 2,
and odd rational primes. The global product is proved from quadratic
reciprocity; neither a Brauer group nor a reciprocity assertion is assumed.
This file does not assert a norm criterion or a quaternion comparison. -/
namespace FourCorner.HilbertArithmeticHigh11

abbrev OddPrime := {p : ℕ // p.Prime ∧ p ≠ 2}
inductive Atom where
  | negOne
  | two
  | prime (p : OddPrime)
  deriving DecidableEq
open Atom

instance (p : OddPrime) : Fact p.val.Prime := ⟨p.property.1⟩

def value : Atom → ℚ
  | negOne => -1
  | two => 2
  | prime p => p.val

def primeSupport : Atom → Finset ℕ
  | negOne => ∅
  | two => ∅
  | prime p => {p.val}

def singleSign (q : ℕ) (s : ℤ) (v : ℕ) : ℤ := if v=q then s else 1

theorem prod_singleSign (S : Finset ℕ) (q : ℕ) (s : ℤ) (hq : q∈S) :
    ∏ v ∈ S, singleSign q s v = s := by
  simp only [singleSign,Finset.prod_ite_eq',if_pos hq]

/-- Explicit local signs on prime generators. Place 0 is the real place;
place 2 is dyadic; the other supported places are the actual odd primes. -/
def generatorSign : Atom → Atom → ℕ → ℤ
  | negOne, negOne, v => singleSign 0 (-1) v * singleSign 2 (-1) v
  | negOne, two, _ => 1
  | two, negOne, _ => 1
  | two, two, _ => 1
  | negOne, prime p, v =>
      singleSign 2 (legendreSym p.val (-1)) v * singleSign p.val (legendreSym p.val (-1)) v
  | prime p, negOne, v =>
      singleSign 2 (legendreSym p.val (-1)) v * singleSign p.val (legendreSym p.val (-1)) v
  | two, prime p, v =>
      singleSign 2 (legendreSym p.val 2) v * singleSign p.val (legendreSym p.val 2) v
  | prime p, two, v =>
      singleSign 2 (legendreSym p.val 2) v * singleSign p.val (legendreSym p.val 2) v
  | prime p, prime q, v =>
      if p=q then
        singleSign 2 (legendreSym p.val (-1)) v * singleSign p.val (legendreSym p.val (-1)) v
      else
        singleSign 2 ((-1 : ℤ)^(p.val/2*(q.val/2))) v *
        singleSign p.val (legendreSym p.val q.val) v *
        singleSign q.val (legendreSym q.val p.val) v

private theorem legendre_neg_sq (p : OddPrime) : (legendreSym p.val (-1))^2=1 := by
  apply legendreSym.sq_one
  simp

private theorem legendre_two_sq (p : OddPrime) : (legendreSym p.val 2)^2=1 := by
  apply legendreSym.sq_one
  have h2 : ¬ p.val ∣ 2 := by
    intro hd
    exact p.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left p.property.1.ne_one)
  have hh : (2 : ZMod p.val) ≠ 0 := by
    exact fun h => h2 ((ZMod.natCast_eq_zero_iff 2 p.val).mp h)
  simpa using hh

/-- Full finite-support product formula on every pair of signed prime generators. -/
theorem generator_reciprocity (x y : Atom) (S : Finset ℕ) (h0 : 0∈S) (h2 : 2∈S)
    (hx : primeSupport x ⊆ S) (hy : primeSupport y ⊆ S) :
    ∏ v ∈ S, generatorSign x y v = 1 := by
  cases x <;> cases y
  · simp only [generatorSign,Finset.prod_mul_distrib,prod_singleSign S 0 (-1) h0,
      prod_singleSign S 2 (-1) h2]; norm_num
  · simp [generatorSign]
  · rename_i q
    have hq : q.val∈S := hy (by simp [primeSupport])
    simp only [generatorSign,Finset.prod_mul_distrib,prod_singleSign S 2 _ h2,
      prod_singleSign S q.val _ hq,← sq]
    exact legendre_neg_sq q
  · simp [generatorSign]
  · simp [generatorSign]
  · rename_i q
    have hq : q.val∈S := hy (by simp [primeSupport])
    simp only [generatorSign,Finset.prod_mul_distrib,prod_singleSign S 2 _ h2,
      prod_singleSign S q.val _ hq,← sq]
    exact legendre_two_sq q
  · rename_i p
    have hp : p.val∈S := hx (by simp [primeSupport])
    simp only [generatorSign,Finset.prod_mul_distrib,prod_singleSign S 2 _ h2,
      prod_singleSign S p.val _ hp,← sq]
    exact legendre_neg_sq p
  · rename_i p
    have hp : p.val∈S := hx (by simp [primeSupport])
    simp only [generatorSign,Finset.prod_mul_distrib,prod_singleSign S 2 _ h2,
      prod_singleSign S p.val _ hp,← sq]
    exact legendre_two_sq p
  · rename_i p q
    have hp : p.val∈S := hx (by simp [primeSupport])
    have hq : q.val∈S := hy (by simp [primeSupport])
    by_cases hpq : p=q
    · simp only [generatorSign,if_pos hpq,Finset.prod_mul_distrib,
        prod_singleSign S 2 _ h2,prod_singleSign S p.val _ hp,← sq]
      exact legendre_neg_sq p
    · simp only [generatorSign,if_neg hpq,Finset.prod_mul_distrib,
        prod_singleSign S 2 _ h2,prod_singleSign S p.val _ hp,prod_singleSign S q.val _ hq]
      have hval : p.val ≠ q.val := by intro hh; exact hpq (Subtype.ext hh)
      have hqr := legendreSym.quadratic_reciprocity p.property.2 q.property.2 hval
      have hpow : ((-1 : ℤ)^(p.val/2*(q.val/2)))^2=1 := by
        rw [← pow_mul, Nat.mul_comm _ 2, pow_mul]; norm_num
      calc
        _ = ((-1 : ℤ)^(p.val/2*(q.val/2))) *
          (legendreSym q.val p.val * legendreSym p.val q.val) := by ring
        _ = ((-1 : ℤ)^(p.val/2*(q.val/2)))^2 := by rw [hqr,pow_two]
        _ = 1 := hpow

/-- Bilinear extension of the explicit generator formulas to finite prime
presentations. Multiplicity is retained; repeated factors represent squares. -/
def rowSign (x : Atom) : List Atom → ℕ → ℤ
  | [], _ => 1
  | y::ys, v => generatorSign x y v * rowSign x ys v

def presentationSign : List Atom → List Atom → ℕ → ℤ
  | [], _, _ => 1
  | x::xs, ys, v => rowSign x ys v * presentationSign xs ys v

def listSupport : List Atom → Finset ℕ
  | [] => ∅
  | x::xs => primeSupport x ∪ listSupport xs

private theorem row_reciprocity (x : Atom) (ys : List Atom) (S : Finset ℕ)
    (h0 : 0∈S) (h2 : 2∈S) (hx : primeSupport x ⊆ S) (hy : listSupport ys ⊆ S) :
    ∏ v ∈ S, rowSign x ys v = 1 := by
  induction ys with
  | nil => simp [rowSign]
  | cons y ys ih =>
    have hy' : primeSupport y ⊆ S := fun _ hh => hy (Finset.mem_union_left _ hh)
    have hys : listSupport ys ⊆ S := fun _ hh => hy (Finset.mem_union_right _ hh)
    simp only [rowSign,Finset.prod_mul_distrib,generator_reciprocity x y S h0 h2 hx hy',ih hys,
      one_mul]

/-- Global reciprocity of the literal arithmetic signs for arbitrary finite
signed prime presentations, proved rather than supplied as a hypothesis. -/
theorem presentation_reciprocity (xs ys : List Atom) (S : Finset ℕ)
    (h0 : 0∈S) (h2 : 2∈S) (hx : listSupport xs ⊆ S) (hy : listSupport ys ⊆ S) :
    ∏ v ∈ S, presentationSign xs ys v = 1 := by
  induction xs with
  | nil => simp [presentationSign]
  | cons x xs ih =>
    have hx' : primeSupport x ⊆ S := fun _ hh => hx (Finset.mem_union_left _ hh)
    have hxs : listSupport xs ⊆ S := fun _ hh => hx (Finset.mem_union_right _ hh)
    simp only [presentationSign,Finset.prod_mul_distrib,row_reciprocity x ys S h0 h2 hx' hy,
      ih hxs,one_mul]

/-- The actual rational number represented by a finite signed prime list. -/
def evalPresentation (xs : List Atom) : ℚ := (xs.map value).prod

def atomOfPrime (p : ℕ) (hp : p.Prime) : Atom :=
  if h : p=2 then two else prime ⟨p,hp,h⟩

@[simp] theorem value_atomOfPrime (p : ℕ) (hp : p.Prime) : value (atomOfPrime p hp)=(p : ℚ) := by
  by_cases hh : p=2
  · simp [atomOfPrime,hh,value]
  · simp [atomOfPrime,hh,value]

def atomList (L : List ℕ) (h : ∀ p ∈ L, p.Prime) : List Atom :=
  L.pmap atomOfPrime h

theorem eval_atomList (L : List ℕ) (h : ∀ p ∈ L, p.Prime) :
    evalPresentation (atomList L h)=(L.prod : ℚ) := by
  induction L with
  | nil => simp [atomList,evalPresentation]
  | cons p L ih =>
    simp only [atomList,List.pmap_cons,evalPresentation,List.map_cons,List.prod_cons,
      value_atomOfPrime,Nat.cast_mul]
    exact congrArg ((p : ℚ)*·) (ih (fun q hq => h q (List.mem_cons_of_mem p hq)))

/-- Existence of a signed prime presentation for every nonzero rational,
with an actual nonzero rational square factor. No squareclass oracle is used. -/
theorem rational_presentation (r : ℚ) (hr : r ≠ 0) :
    ∃ xs : List Atom, ∃ s : ℚ, s ≠ 0 ∧ r=evalPresentation xs*s^2 := by
  have positive_case (r : ℚ) (hr : 0<r) :
      ∃ xs : List Atom, ∃ s : ℚ, s ≠ 0 ∧ r=evalPresentation xs*s^2 := by
    obtain ⟨a,b,ha,hb,hab⟩ := positive_rat_nat_fraction hr
    let n := a*b
    have hn : n ≠ 0 := Nat.ne_of_gt (Nat.mul_pos ha hb)
    let xs := atomList n.primeFactorsList (fun _ hh => Nat.prime_of_mem_primeFactorsList hh)
    have hxs : evalPresentation xs=(n : ℚ) := by
      rw [eval_atomList,Nat.prod_primeFactorsList hn]
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    refine ⟨xs,1/(b : ℚ),one_div_ne_zero hbq,?_⟩
    rw [hxs,hab]
    dsimp [n]
    push_cast
    field_simp
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · obtain ⟨xs,s,hs,he⟩ := positive_case (-r) (neg_pos.mpr hneg)
    refine ⟨negOne::xs,s,hs,?_⟩
    simp only [evalPresentation,List.map_cons,List.prod_cons,value]
    change r= -1*evalPresentation xs*s^2
    linear_combination -he
  · exact positive_case r hpos

theorem generatorSign_one_outside (x y : Atom) (v : ℕ) (h0 : v≠0) (h2 : v≠2)
    (hx : v∉primeSupport x) (hy : v∉primeSupport y) : generatorSign x y v=1 := by
  cases x <;> cases y <;> simp_all [generatorSign,singleSign,primeSupport]

private theorem rowSign_one_outside (x : Atom) (ys : List Atom) (v : ℕ)
    (h0 : v≠0) (h2 : v≠2) (hx : v∉primeSupport x) (hy : v∉listSupport ys) :
    rowSign x ys v=1 := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [listSupport,Finset.mem_union,not_or] at hy
    rw [rowSign,generatorSign_one_outside x y v h0 h2 hx hy.1,ih hy.2,one_mul]

theorem presentationSign_one_outside (xs ys : List Atom) (v : ℕ)
    (h0 : v≠0) (h2 : v≠2) (hx : v∉listSupport xs) (hy : v∉listSupport ys) :
    presentationSign xs ys v=1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [listSupport,Finset.mem_union,not_or] at hx
    rw [presentationSign,rowSign_one_outside x ys v h0 h2 hx.1 hy,ih hx.2,one_mul]

/-- A constructive arithmetic reciprocity witness for every pair of actual
nonzero rationals. The finite product includes all its local support. -/
theorem rational_presentation_reciprocity (a b : ℚ) (ha : a≠0) (hb : b≠0) :
    ∃ xs ys : List Atom, ∃ s t : ℚ,
      s≠0 ∧ t≠0 ∧ a=evalPresentation xs*s^2 ∧ b=evalPresentation ys*t^2 ∧
      (∏ v ∈ ({0,2} ∪ listSupport xs ∪ listSupport ys),presentationSign xs ys v)=1 ∧
      (∀ v, v∉({0,2} ∪ listSupport xs ∪ listSupport ys) → presentationSign xs ys v=1) := by
  obtain ⟨xs,s,hs,he⟩ := rational_presentation a ha
  obtain ⟨ys,t,ht,hf⟩ := rational_presentation b hb
  refine ⟨xs,ys,s,t,hs,ht,he,hf,?_,?_⟩
  · apply presentation_reciprocity
    · simp
    · simp
    · intro v hv; simp [hv]
    · intro v hv; simp [hv]
  · intro v hv
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hv
    exact presentationSign_one_outside xs ys v hv.1.1.1 hv.1.1.2 hv.1.2 hv.2

#print axioms generator_reciprocity
#print axioms presentation_reciprocity
#print axioms rational_presentation
#print axioms rational_presentation_reciprocity
end FourCorner.HilbertArithmeticHigh11
