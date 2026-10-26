import RefinedFiniteExistence
import RefinedPaperInterfaces

noncomputable section
namespace FourCorner.CriticalRefinedFull
open CriticalRefinedWave27 CriticalRefinedCompletion RefinedFiniteExistence
variable {p:ℕ} [Fact p.Prime]

/-- The original finite pattern already has a NONZERO doubled product, so
its square is literally in F_p^{times2}, as in the manuscript. -/
theorem refined_pattern_iff_unit_product (hmod:p%4=1) :
    RefinedPattern p ↔ ∃i b v0 v1 v2 v3:ZMod p,
      SignedPattern i b v0 v1 v2 v3 ∧ v0≠0 ∧ v1≠0 ∧ v2≠0 ∧ v3≠0 ∧
      IsSquare (2*(v0*v3+v1*v2)) ∧ 2*(v0*v3+v1*v2)≠0 := by
  constructor
  · rintro ⟨i,b,v0,v1,v2,v3,hp,h0,h1,h2,h3,hs⟩
    have hp2:p≠2 := by omega
    have ht:(2:ZMod p)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp2)
    exact ⟨i,b,v0,v1,v2,v3,hp,h0,h1,h2,h3,hs,mul_ne_zero ht (signed_product_nonzero hp).1⟩
  · rintro ⟨i,b,v0,v1,v2,v3,hp,h0,h1,h2,h3,hs,hn⟩
    exact ⟨i,b,v0,v1,v2,v3,hp,h0,h1,h2,h3,hs⟩

/-- Exact prime classification of the ORIGINAL finite signed refined pattern. -/
theorem finite_iff (hmod:p%4=1) :
    p∉({5,13,17}:Finset ℕ) ↔ RefinedPattern p := by
  constructor
  · intro h
    have hn:p≠5 ∧ p≠13 ∧ p≠17 := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using h
    exact allowed_refined_pattern hmod hn.1 hn.2.1 hn.2.2
  · intro h
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using refined_necessary h

/-- Full thm:crit-refined: all three original clauses are equivalent.
The local-family clause is the frozen literal set of primitive strict
rational pairs, at EVERY positive depth, with one SAME actual root tuple
and both NONZERO p-adic product-square conditions. -/
theorem thm_crit_refined (hmod:p%4=1) :
    (p∉({5,13,17}:Finset ℕ) ↔ RefinedPattern p) ∧
    (RefinedPattern p ↔ ∀s:ℕ,1≤s→(PaperRefinedPairs p s).Infinite) := by
  have hp2:p≠2 := by omega
  exact ⟨finite_iff hmod,refined_pattern_iff_local_families hp2⟩

/-- Direct equivalence of clauses(i) and(iii), without a missing finite
pattern-existence certificate or any extra source/rank hypothesis. -/
theorem exclusions_iff_infinite_pairs (hmod:p%4=1) :
    p∉({5,13,17}:Finset ℕ) ↔ ∀s:ℕ,1≤s→(PaperRefinedPairs p s).Infinite :=
  (finite_iff hmod).trans (refined_pattern_iff_local_families (by omega))

/-- Literal finite nonzero-square wording for clause(ii), retained alongside
the exact original predicate and actual-family theorem above. -/
theorem exclusions_iff_literal_pattern (hmod:p%4=1) :
    p∉({5,13,17}:Finset ℕ) ↔ ∃i b v0 v1 v2 v3:ZMod p,
      SignedPattern i b v0 v1 v2 v3 ∧ v0≠0 ∧ v1≠0 ∧ v2≠0 ∧ v3≠0 ∧
      IsSquare (2*(v0*v3+v1*v2)) ∧ 2*(v0*v3+v1*v2)≠0 :=
  (finite_iff hmod).trans (refined_pattern_iff_unit_product hmod)

#print axioms refined_pattern_iff_unit_product
#print axioms finite_iff
#print axioms thm_crit_refined
#print axioms exclusions_iff_infinite_pairs
#print axioms exclusions_iff_literal_pattern
end FourCorner.CriticalRefinedFull
