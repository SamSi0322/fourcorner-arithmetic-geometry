import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic
namespace FourCorner.SqrtTwoEuclidean
abbrev R := Zsqrtd (2 : ℤ)

private instance twoNonsquare : Zsqrtd.Nonsquare 2 := ⟨by
  intro n hn
  by_cases h : n ≤ 1
  · interval_cases n <;> norm_num at hn
  · have hh : 2 ≤ n := by omega
    nlinarith⟩

private theorem two_not_int_square : ∀ n : ℤ, (2 : ℤ) ≠ n*n := by
  intro n hn
  have hlo : -1 ≤ n := by nlinarith
  have hhi : n ≤ 1 := by nlinarith
  interval_cases n <;> norm_num at hn

theorem norm_ne_zero {x : R} (hx : x ≠ 0) : x.norm ≠ 0 :=
  fun hh => hx ((Zsqrtd.norm_eq_zero two_not_int_square x).mp hh)

def quotient (x y : R) : R :=
  ⟨round (((x*star y).re : ℚ) / y.norm),
   round (((x*star y).im : ℚ) / y.norm)⟩
def remainder (x y : R) : R := x-y*quotient x y

theorem rounding_norm_lt_one (a b : ℚ) :
    |(a-round a)^2-2*(b-round b)^2| < 1 := by
  have ha := abs_sub_round a
  have hb := abs_sub_round b
  have ha2 : (a-round a)^2 ≤ (1/4:ℚ) := by
    have hh := (sq_le_sq).mpr (show |a-round a| ≤ |(1/2:ℚ)| by simpa using ha)
    norm_num at hh
    exact hh
  have hb2 : (b-round b)^2 ≤ (1/4:ℚ) := by
    have hh := (sq_le_sq).mpr (show |b-round b| ≤ |(1/2:ℚ)| by simpa using hb)
    norm_num at hh
    exact hh
  apply abs_lt.mpr
  constructor <;> nlinarith [sq_nonneg (a-round a),sq_nonneg (b-round b)]

theorem remainder_norm_formula (x y : R) (hy : y ≠ 0) :
    (Zsqrtd.norm (remainder x y) : ℚ) = (y.norm : ℚ) *
      (((((x*star y).re : ℚ)/y.norm)-round (((x*star y).re : ℚ)/y.norm))^2 -
       2*((((x*star y).im : ℚ)/y.norm)-round (((x*star y).im : ℚ)/y.norm))^2) := by
  have hny : (y.norm : ℚ) ≠ 0 := by exact_mod_cast norm_ne_zero hy
  have heN : (y.norm : ℚ) = (y.re : ℚ)^2-2*(y.im : ℚ)^2 := by
    simp only [Zsqrtd.norm]
    push_cast
    ring
  change (((remainder x y).re * (remainder x y).re -
    2*(remainder x y).im*(remainder x y).im : ℤ) : ℚ) = _
  unfold remainder quotient
  generalize hA : round (((x*star y).re : ℚ)/y.norm) = A
  generalize hB : round (((x*star y).im : ℚ)/y.norm) = B
  simp only [Zsqrtd.re_sub,Zsqrtd.im_sub,
    Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.re_star,Zsqrtd.im_star]
  push_cast
  field_simp [hny]
  rw [heN]
  ring

theorem remainder_norm_lt (x y : R) (hy : y ≠ 0) :
    (remainder x y).norm.natAbs < y.norm.natAbs := by
  have hny : (y.norm : ℚ) ≠ 0 := by exact_mod_cast norm_ne_zero hy
  have hh : |(Zsqrtd.norm (remainder x y) : ℚ)| < |(y.norm : ℚ)| := by
    rw [remainder_norm_formula x y hy,abs_mul]
    have ht := rounding_norm_lt_one (((x*star y).re : ℚ)/y.norm)
      (((x*star y).im : ℚ)/y.norm)
    exact (mul_lt_mul_of_pos_left ht (abs_pos.mpr hny)).trans_eq (mul_one _)
  apply Int.ofNat_lt.mp
  rw [Int.natCast_natAbs,Int.natCast_natAbs]
  exact_mod_cast hh

theorem norm_le_norm_mul (x y : R) (hy : y ≠ 0) :
    x.norm.natAbs ≤ (x*y).norm.natAbs := by
  rw [Zsqrtd.norm_mul,Int.natAbs_mul]
  have hn : 1 ≤ y.norm.natAbs := Nat.one_le_iff_ne_zero.mpr
    (by intro hh; exact norm_ne_zero hy (Int.natAbs_eq_zero.mp hh))
  exact Nat.le_mul_of_pos_right _ hn

instance : EuclideanDomain R :=
  { (inferInstance : CommRing R), (inferInstance : Nontrivial R) with
    quotient := quotient
    remainder := remainder
    quotient_zero := by intro x; simp [quotient,Zsqrtd.norm]; rfl
    quotient_mul_add_remainder_eq := fun x y => by simp [remainder]
    r := fun x y => x.norm.natAbs < y.norm.natAbs
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := remainder_norm_lt
    mul_left_not_lt := fun a b hb => not_lt_of_ge (norm_le_norm_mul a b hb) }
theorem nat_prime_not_prime_of_two_square (p : ℕ) [hp : Fact p.Prime]
    (hs : IsSquare (2 : ZMod p)) : ¬ Prime (p : R) := by
  obtain ⟨u,hu⟩ := hs
  let k : ℤ := u.val
  have hk : (k : ZMod p)=u := by simp [k]
  have hd : (p : ℤ) ∣ k^2-2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [hk,pow_two,←hu,sub_self]
  have hno (e : ℤ) (he : e=1 ∨ e= -1) : ¬ (p : R) ∣ (⟨k,e⟩ : R) := by
    rintro ⟨x,hx⟩
    have him := congrArg Zsqrtd.im hx
    simp only [Zsqrtd.im_mul,Zsqrtd.im_natCast,Zsqrtd.re_natCast,zero_mul,add_zero] at him
    have hpdiv : (p : ℤ) ∣ e := ⟨x.im,him⟩
    have hh : (p : ℤ) ∣ 1 := by
      rcases he with he | he
      · rwa [he] at hpdiv
      · have hh : (p : ℤ) ∣ -(1 : ℤ) := by simpa [he] using hpdiv
        exact (dvd_neg).mp hh
    have hh' : p ∣ 1 := by exact_mod_cast hh
    exact hp.out.ne_one (Nat.dvd_one.mp hh')
  intro hprime
  have hprod : (p : R) ∣ (⟨k,1⟩ : R)*(⟨k,-1⟩ : R) := by
    obtain ⟨z,hz⟩ := hd
    refine ⟨(z : R), ?_⟩
    apply Zsqrtd.ext
    · simp only [Zsqrtd.re_mul,Zsqrtd.re_natCast,Zsqrtd.im_natCast,
        Zsqrtd.re_intCast,Zsqrtd.im_intCast]
      nlinarith [hz]
    · simp
  exact (hprime.dvd_or_dvd hprod).elim (hno 1 (Or.inl rfl)) (hno (-1) (Or.inr rfl))

/-- Every rational prime that splits modulo p is an absolute norm of a
nonunit in the genuine norm-Euclidean ring Z[√2]. -/
theorem split_prime_abs_norm (p : ℕ) [hp : Fact p.Prime]
    (hs : IsSquare (2 : ZMod p)) : ∃ x : R, x.norm.natAbs=p := by
  have hpu : ¬ IsUnit (p : R) := by
    intro hh
    have hn := Zsqrtd.norm_eq_one_iff.mpr hh
    rw [Zsqrtd.norm_natCast,Int.natAbs_mul] at hn
    norm_num at hn
    nlinarith [hp.out.one_lt]
  have hpi : ¬ Irreducible (p : R) := by
    intro hh
    exact nat_prime_not_prime_of_two_square p hs (irreducible_iff_prime.mp hh)
  have hab : ∃ a b : R, (p : R)=a*b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    simpa [irreducible_iff,hpu,not_forall,not_or] using hpi
  obtain ⟨a,b,hab,hau,hbu⟩ := hab
  refine ⟨a, ?_⟩
  apply ((hp.out.mul_eq_prime_sq_iff (mt Zsqrtd.norm_eq_one_iff.mp hau)
    (mt Zsqrtd.norm_eq_one_iff.mp hbu)).mp ?_).1
  have hn := congrArg (fun z : R => z.norm.natAbs) hab
  simpa only [Zsqrtd.norm_natCast,Zsqrtd.norm_mul,Int.natAbs_mul,Int.natAbs_natCast,pow_two] using hn.symm

#print axioms split_prime_abs_norm
#print axioms remainder_norm_lt
end FourCorner.SqrtTwoEuclidean
