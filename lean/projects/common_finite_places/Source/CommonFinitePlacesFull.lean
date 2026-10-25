import GoodPrimePoints

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.LocalPointCompatibility
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The finite tests are EXACTLY equivalent to solubility at the real
place and every prime on the same actual covers. -/
theorem everywhere_eq_finite (t : ℚ) (ht : 1<t)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    everywhereTwists t h0 h1 hm = finiteTestTwists t h0 h1 hm := by
  apply Finset.Subset.antisymm (everywhere_subset_finite t h0 h1 hm)
  intro κ hκ
  obtain ⟨hκ,hr,hp⟩ := Finset.mem_filter.mp hκ
  apply Finset.mem_filter.mpr
  refine ⟨hκ,hr,?_⟩
  intro p hprime
  by_cases hb : badPrimeCondition t p
  · exact hp p hprime hb
  · letI : Fact p.Prime := ⟨hprime⟩
    have hout : p ∉ exceptionalPrimes t := by
      intro hh
      exact hb ((mem_exceptionalPrimes t p).mp hh).2
    exact good_prime_point ht hκ h0 h1 hm hout

/-- Full prop:common-finite-places on the exact finite K_t, actual native
Q-models, actual R/Qp-valued points and actual rational points of D_t.
The proof uses a finite-field rational place and explicit smooth local
charts, rather than assuming a good-reduction model or a local point. -/
theorem common_finite_places (t : ℚ) (ht : 1<t)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    {p : ℕ | p.Prime ∧ badPrimeCondition t p}.Finite ∧
    (∀ p, p ∈ exceptionalPrimes t ↔ p.Prime ∧
      (p ≤ 1153 ∨ padicValRat p t ≠ 0 ∨ padicValRat p (t-1) ≠ 0 ∨ padicValRat p (t+1) ≠ 0)) ∧
    (∀ κ ∈ Genus17Support.twists t, ∀ (p : ℕ) (hp : p.Prime),
      p ∉ exceptionalPrimes t → padicPoint (Genus17Geometry.curve t κ h0 h1 hm) p hp) ∧
    everywhereTwists t h0 h1 hm = finiteTestTwists t h0 h1 hm ∧
    (everywhereTwists t h0 h1 hm = ∅ →
      IsEmpty (Spec (CommRingCat.of ℚ) ⟶ CommonPostFiniteP1.commonCurve t h0 h1 hm)) := by
  refine ⟨exceptional_primes_finite t,?_,?_,everywhere_eq_finite t ht h0 h1 hm,?_⟩
  · intro p
    exact mem_exceptionalPrimes t p
  · intro κ hκ p hp hout
    letI : Fact p.Prime := ⟨hp⟩
    exact good_prime_point ht hκ h0 h1 hm hout
  · exact everywhere_empty_no_rational_point t ht h0 h1 hm

end FourCorner.LocalPointCompatibility
#print axioms FourCorner.LocalPointCompatibility.everywhere_eq_finite
#print axioms FourCorner.LocalPointCompatibility.common_finite_places
