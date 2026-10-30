import FourCorner.SqrtTwoEuclidean
import FourCorner.HasseNormWitness
import FourCorner.RationalSquarefree
import FourCorner.CommonRootPadicVal
import FourCorner.PadicResidueSquareBasic
import Mathlib.Tactic
namespace FourCorner.SqrtTwoGlobalNorm
open HasseNormWitness

theorem integer_ring_norm (z : SqrtTwoEuclidean.R) :
    ∃ x : SqrtTwo ℚ, x.norm=(z.norm : ℚ) := by
  refine ⟨⟨z.re,z.im⟩, ?_⟩
  simp only [QuadraticAlgebra.norm_def,Zsqrtd.norm]
  push_cast
  ring

theorem split_prime_norm (p : ℕ) [Fact p.Prime] (hs : IsSquare (2 : ZMod p)) :
    ∃ x : SqrtTwo ℚ, x.norm=(p : ℚ) := by
  obtain ⟨z,hz⟩ := SqrtTwoEuclidean.split_prime_abs_norm p hs
  have hh : z.norm.natAbs=(p : ℤ).natAbs := by simpa using hz
  rcases Int.natAbs_eq_natAbs_iff.mp hh with hh | hh
  · simpa [hh] using integer_ring_norm z
  · have hn : ∃ x : SqrtTwo ℚ, x.norm= -(p : ℚ) := by
      simpa [hh] using integer_ring_norm z
    simpa using exists_norm_neg hn

theorem norm_two : ∃ x : SqrtTwo ℚ, x.norm=2 := by
  exact ⟨⟨2,1⟩,by norm_num [QuadraticAlgebra.norm_def]⟩

theorem exists_norm_mul {a b : ℚ} (ha : ∃ x : SqrtTwo ℚ, x.norm=a)
    (hb : ∃ x : SqrtTwo ℚ, x.norm=b) : ∃ x : SqrtTwo ℚ, x.norm=a*b := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  exact ⟨x*y,by rw [map_mul,hx,hy]⟩

theorem exists_norm_pow {a : ℚ} (ha : ∃ x : SqrtTwo ℚ, x.norm=a) (n : ℕ) :
    ∃ x : SqrtTwo ℚ, x.norm=a^n := by
  obtain ⟨x,hx⟩ := ha
  exact ⟨x^n,by rw [map_pow,hx]⟩

theorem prime_power_norm (p k : ℕ) (hp : p.Prime)
    (he : p ≠ 2 → ¬ IsSquare (2 : ZMod p) → Even k) :
    ∃ x : SqrtTwo ℚ, x.norm=(p : ℚ)^k := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p=2
  · subst p
    exact exists_norm_pow norm_two k
  by_cases hs : IsSquare (2 : ZMod p)
  · exact exists_norm_pow (split_prime_norm p hs) k
  obtain ⟨j,hj⟩ := he hp2 hs
  refine ⟨algebraMap ℚ (SqrtTwo ℚ) ((p : ℚ)^j), ?_⟩
  rw [QuadraticAlgebra.norm_algebraMap,hj]
  simp [pow_add,pow_two]

/-- An explicit norm construction from natural prime factorization, using
the proved Euclidean split-prime norm theorem. No local-global axiom occurs. -/
theorem natural_norm_of_even_inert (n : ℕ) (hn : n ≠ 0)
    (he : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ IsSquare (2 : ZMod p) →
      Even (n.factorization p)) :
    ∃ x : SqrtTwo ℚ, x.norm=(n : ℚ) := by
  have hprod : ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) →
      ∃ x : SqrtTwo ℚ, x.norm= ∏ p ∈ S, (p : ℚ)^(n.factorization p) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun _ => ⟨1,by simp⟩
    | @insert p S hpS ih =>
      intro hprime
      have hp := hprime p (Finset.mem_insert_self p S)
      have hpn := prime_power_norm p (n.factorization p) hp (he p hp)
      have hSn := ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
      simpa only [Finset.prod_insert hpS] using exists_norm_mul hpn hSn
  have hpS : ∀ p ∈ n.factorization.support, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (by simpa using hp)
  obtain ⟨x,hx⟩ := hprod n.factorization.support hpS
  refine ⟨x,hx.trans ?_⟩
  have hnf := congrArg (fun z : ℕ => (z : ℚ)) (Nat.prod_factorization_pow_eq_self hn)
  simpa only [Finsupp.prod,Nat.cast_prod,Nat.cast_pow] using hnf

/-- Inert residue classes really are nonsquares in the completed field. -/
theorem nonsquare_two_completion {p : ℕ} [Fact p.Prime]
    (hs : ¬ IsSquare (2 : ZMod p)) : ¬ IsSquare (2 : ℚ_[p]) := by
  intro hh
  have hn : IsSquare (PadicInt.toZMod (2 : ℤ_[p])) :=
    padicInt_isSquare_toZMod_of_isSquare_coe 2 hh
  have he : PadicInt.toZMod (2 : ℤ_[p]) = (2 : ZMod p) := map_ofNat _ 2
  rw [he] at hn
  exact hs hn

/-- Constructive global norm sufficiency for every positive rational number.
The construction uses prime factorization of numerator times denominator and
the norm-Euclidean split-prime theorem, replacing Hasse norm reciprocity. -/
theorem positive_rat_norm_of_even_inert (r : ℚ) (hr : 0<r)
    (he : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ IsSquare (2 : ZMod p) →
      Even (padicValRat p r)) :
    ∃ x : SqrtTwo ℚ, x.norm=r := by
  obtain ⟨a,b,ha,hb,hrab⟩ := positive_rat_nat_fraction hr
  let n : ℕ := a*b
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.mul_pos ha hb)
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hrep : (n : ℚ)=r*(b : ℚ)^2 := by
    rw [hrab]
    dsimp [n]
    push_cast
    field_simp
  have hnpar : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ IsSquare (2 : ZMod p) →
      Even (n.factorization p) := by
    intro p hp hp2 hns
    letI : Fact p.Prime := ⟨hp⟩
    have hrp : (r : ℚ_[p]) ≠ 0 := by exact_mod_cast hr.ne'
    have hbp : (b : ℚ_[p]) ≠ 0 := by exact_mod_cast hb.ne'
    have heq : (n : ℚ_[p])=(r : ℚ_[p])*(b : ℚ_[p])^2 := by exact_mod_cast hrep
    have hval := congrArg Padic.valuation heq
    rw [Padic.valuation_mul hrp (pow_ne_zero _ hbp),Padic.valuation_pow,
      Padic.valuation_natCast,Padic.valuation_ratCast] at hval
    rw [← Nat.factorization_def n hp] at hval
    obtain ⟨k,hk⟩ := he p hp hp2 hns
    rw [Nat.even_iff]
    omega
  obtain ⟨x,hx⟩ := natural_norm_of_even_inert n hn hnpar
  have hbnorm : ∃ y : SqrtTwo ℚ, y.norm=(b : ℚ)^2 :=
    ⟨algebraMap ℚ (SqrtTwo ℚ) (b : ℚ),QuadraticAlgebra.norm_algebraMap _⟩
  obtain ⟨y,hy⟩ := exists_norm_div (pow_ne_zero _ hbq) ⟨x,hx⟩ hbnorm
  refine ⟨y,hy.trans ?_⟩
  rw [hrep]
  field_simp

#print axioms positive_rat_norm_of_even_inert
#print axioms split_prime_norm
#print axioms natural_norm_of_even_inert
#print axioms nonsquare_two_completion
end FourCorner.SqrtTwoGlobalNorm
