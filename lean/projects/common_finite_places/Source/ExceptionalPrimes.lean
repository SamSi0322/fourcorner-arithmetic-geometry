import LocalPointCompatibility

noncomputable section
namespace FourCorner.LocalPointCompatibility
attribute [local instance] Classical.propDecidable

def rationalPrimeSupportBound (q : ℚ) : Finset ℕ :=
  q.num.natAbs.primeFactors ∪ q.den.primeFactors

theorem nonzero_valuation_mem_support (q : ℚ) (p : ℕ) (hp : p.Prime)
    (hv : padicValRat p q ≠ 0) : p ∈ rationalPrimeSupportBound q := by
  by_cases hq : q = 0
  · subst q
    exact False.elim (hv (by simp))
  have hn : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  by_contra h
  have hnum : ¬ p ∣ q.num.natAbs := by
    intro hd
    exact h (Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp,hd,hn⟩))
  have hden : ¬ p ∣ q.den := by
    intro hd
    exact h (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp,hd,q.den_nz⟩))
  apply hv
  simp only [padicValRat,padicValInt,padicValNat.eq_zero_of_not_dvd hnum,
    padicValNat.eq_zero_of_not_dvd hden,Nat.cast_zero,sub_self]

def exceptionalPrimeCandidates (t : ℚ) : Finset ℕ :=
  Finset.range 1154 ∪ rationalPrimeSupportBound t ∪
    rationalPrimeSupportBound (t-1) ∪ rationalPrimeSupportBound (t+1)

/-- The exact prime test set in the paper, exhibited as a genuine finite set. -/
def exceptionalPrimes (t : ℚ) : Finset ℕ :=
  (exceptionalPrimeCandidates t).filter fun p => p.Prime ∧ badPrimeCondition t p

theorem mem_exceptionalPrimes (t : ℚ) (p : ℕ) :
    p ∈ exceptionalPrimes t ↔ p.Prime ∧ badPrimeCondition t p := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨hp,hbad⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,hp,hbad⟩
    unfold exceptionalPrimeCandidates
    simp only [Finset.mem_union]
    rcases hbad with hs | ht | hm | hp1
    · exact Or.inl (Or.inl (Or.inl (Finset.mem_range.mpr (by omega))))
    · exact Or.inl (Or.inl (Or.inr (nonzero_valuation_mem_support t p hp ht)))
    · exact Or.inl (Or.inr (nonzero_valuation_mem_support (t-1) p hp hm))
    · exact Or.inr (nonzero_valuation_mem_support (t+1) p hp hp1)

theorem exceptional_primes_finite (t : ℚ) :
    {p : ℕ | p.Prime ∧ badPrimeCondition t p}.Finite := by
  apply (exceptionalPrimes t).finite_toSet.subset
  intro p hp
  exact (mem_exceptionalPrimes t p).mpr hp

theorem outside_exceptionalPrimes {t : ℚ} {p : ℕ} (hp : p.Prime)
    (hout : p ∉ exceptionalPrimes t) :
    1153 < p ∧ padicValRat p t = 0 ∧ padicValRat p (t-1) = 0 ∧ padicValRat p (t+1) = 0 := by
  have h := not_and.mp ((mem_exceptionalPrimes t p).not.mp hout) hp
  simp only [badPrimeCondition,not_or,not_not,not_le] at h
  exact h

end FourCorner.LocalPointCompatibility
#print axioms FourCorner.LocalPointCompatibility.mem_exceptionalPrimes
#print axioms FourCorner.LocalPointCompatibility.exceptional_primes_finite
#print axioms FourCorner.LocalPointCompatibility.outside_exceptionalPrimes
