import CommonExclusion

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory

namespace FourCorner.CommonExclusionPaper

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- Squarefreeness of a product of primes gives the indexed distinctness used
by the residue matrix. -/
theorem prime_tuple_injective_of_squarefree {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hs : Squarefree (∏ i, p i)) :
    Function.Injective p := by
  intro i j hij
  by_contra hne
  have hd : p i * p j ∣ ∏ k, p k := by
    simpa [Finset.prod_insert, hne] using
      (Finset.prod_dvd_prod_of_subset ({i, j} : Finset (Fin r)) Finset.univ p (by simp))
  have hu : IsUnit (p j) := hs (p j) (by simpa [hij] using hd)
  exact (hp j).ne_one (Nat.isUnit_iff.mp hu)

/-- The paper formulation with an explicit squarefree kernel Delta, rather
than an independently supplied injectivity premise for its prime tuple. -/
theorem common_exclusion_squarefree {t : ℚ} (ht : 1 < t) {r : ℕ}
    (Delta : ℕ) (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime)
    (hprod : ∏ i, p i = Delta) (hs : Squarefree Delta)
    (hpmod : ∀ i, p i % 8 = 1 ∨ p i % 8 = 7)
    (hgt : 1 < Delta) (hmod : Delta % 8 = 1)
    (hdisc : ∃ qD : ℚ, qD ≠ 0 ∧ t ^ 2 - 1 = (Delta : ℚ) * qD ^ 2)
    (hrank : (primeLegendreMatrix p hp).rank = r - 1)
    (htint : ‖(t : ℚ_[37])‖ ≤ 1)
    (htres : padicResidue (t : ℚ_[37]) htint = 14 ∨
      padicResidue (t : ℚ_[37]) htint = -14 ∨
      padicResidue (t : ℚ_[37]) htint = 16 ∨
      padicResidue (t : ℚ_[37]) htint = -16) :
    IsEmpty (Spec (.of ℚ) ⟶ CommonPostFiniteP1.commonCurve t
      (by linarith) (by linarith) (by linarith)) := by
  have hsprod : Squarefree (∏ i, p i) := by rwa [hprod]
  exact CommonExclusion.common_exclusion ht p hp
    (prime_tuple_injective_of_squarefree p hp hsprod) hpmod
    (by simpa only [hprod] using hgt) (by simpa only [hprod] using hmod)
    (by simpa only [hprod] using hdisc) hrank htint htres

#print axioms prime_tuple_injective_of_squarefree
#check common_exclusion_squarefree
#print axioms common_exclusion_squarefree

end FourCorner.CommonExclusionPaper
