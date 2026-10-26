import RefinedSignedFamily
import RefinedPadicConverse

noncomputable section
namespace FourCorner.CriticalRefinedCompletion
open CriticalRefinedWave27 CriticalCRTWave25
variable {p : ℕ} [Fact p.Prime]

/-- Literal local triple for clause(iii) of thm:crit-refined. Both square
conditions are explicitly NONZERO; t is the original same-tuple expression. -/
def PaperRefinedTriple (p : ℕ) [Fact p.Prime] (s : ℕ) (X Y L : ℤ) : Prop :=
  0<X ∧ 0<Y ∧ X<L ∧ Y<L ∧ Int.gcd (Int.gcd X Y:ℤ) L=1 ∧
    padicValInt p L=2*s ∧ ∃ A : Fin 4 → ℚ_[p],
      (∀ j,A j^2=(criticalRadicands X Y L j:ℚ_[p]) ∧ (A j).valuation=(s:ℤ)) ∧
      IsSquare (2*oppositeParameter A L) ∧ 2*oppositeParameter A L≠0 ∧
      IsSquare (2*(oppositeParameter A L+1)) ∧ 2*(oppositeParameter A L+1)≠0

def PaperRefinedPairs (p : ℕ) [Fact p.Prime] (s : ℕ) : Set (ℚ×ℚ) :=
  {z | ∃ X Y L : ℤ,PaperRefinedTriple p s X Y L ∧ z=((X:ℚ)/L,(Y:ℚ)/L)}

/-- Original signed residue clause(ii) implies the literal infinite actual
rational-pair clause(iii), at EVERY unrestricted positive valuation depth. -/
theorem refined_pattern_infinite_pairs (hodd : p≠2) (hpat : RefinedPattern p)
    (s : ℕ) (hs : 1≤s) : (PaperRefinedPairs p s).Infinite := by
  obtain ⟨i,b,v0,v1,v2,v3,hsp,h0,h1,h2,h3,hprod⟩ :=hpat
  let V : Fin 4 → ZMod p := ![v0,v1,v2,v3]
  have hV : ∀ j,V j≠0 := by intro j;fin_cases j <;> simp [V,h0,h1,h2,h3]
  have hspV : SignedPattern i b (V 0) (V 1) (V 2) (V 3) := by simpa [V] using hsp
  have hprodV : IsSquare (2*(V 0*V 3+V 1*V 2)) := by simpa [V] using hprod
  obtain ⟨X,Y,a,m,hX,hY,ha,hm,hall,hinj⟩ :=signed_refined_family hodd s hs i b V hspV hV hprodV
  have hr (k : ℕ) : PaperRefinedTriple p s X Y (denominator a m k) := by
    obtain ⟨hXL,hYL,hg,hval,u,A,hu,hA,hroot,hpair⟩ :=hall k
    obtain ⟨hXz,hYz,hXLz,hYLz,hgz⟩ :=integer_primitive_interior X Y _ hX hY hXL hYL hg
    exact ⟨hXz,hYz,hXLz,hYLz,hgz,
      by simpa only [padicValInt,Int.natAbs_natCast] using hval,A,hroot,hpair⟩
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨k,rfl⟩
  exact ⟨X,Y,denominator a m k,hr k,rfl⟩

/-- The same family also gives literally infinitely many primitive strict
integer triples, if that stronger form is useful for the final assembly. -/
theorem refined_pattern_infinite_triples (hodd : p≠2) (hpat : RefinedPattern p)
    (s : ℕ) (hs : 1≤s) :
    {t : ℤ×ℤ×ℤ | PaperRefinedTriple p s t.1 t.2.1 t.2.2}.Infinite := by
  have h:=refined_pattern_infinite_pairs hodd hpat s hs
  by_contra! ht
  have hf : (fun t : ℤ×ℤ×ℤ=>((t.1:ℚ)/t.2.2,(t.2.1:ℚ)/t.2.2)) ''
      {t : ℤ×ℤ×ℤ | PaperRefinedTriple p s t.1 t.2.1 t.2.2} = PaperRefinedPairs p s := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t.1,t.2.1,t.2.2,ht,rfl⟩
    · rintro ⟨X,Y,L,htr,rfl⟩
      exact ⟨(X,Y,L),htr,rfl⟩
  exact h (hf ▸ ht.image _)

/-- One literal positive-depth local realization gives clause(ii) and all
three exclusions, with its original Int gcd and SAME actual completed tuple. -/
theorem paper_refined_local_reverse (hodd : p≠2) (s : ℕ) (hs : 1≤s)
    (X Y L : ℤ) (hlocal : PaperRefinedTriple p s X Y L) :
    RefinedPattern p ∧ p≠5 ∧ p≠13 ∧ p≠17 := by
  obtain ⟨_,_,_,_,hg,hL,A,hroot,ht,_⟩ :=hlocal
  have hg' : Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs=1 := by
    simpa only [Int.gcd_def,Int.natAbs_natCast] using hg
  have hpat:=refined_pattern_of_padic_roots hodd X Y L s hs A hg' hL hroot ht
  exact ⟨hpat,refined_necessary hpat⟩

/-- The paper's literal infinite-pair clause(iii) implies clause(ii) and
all exclusions. No finite-field existence direction is silently assumed. -/
theorem paper_refined_infinite_reverse (hodd : p≠2)
    (hlocal : ∀ s : ℕ,1≤s→(PaperRefinedPairs p s).Infinite) :
    RefinedPattern p ∧ p≠5 ∧ p≠13 ∧ p≠17 := by
  obtain ⟨z,X,Y,L,htr,hz⟩ :=(hlocal 1 le_rfl).nonempty
  exact paper_refined_local_reverse hodd 1 le_rfl X Y L htr

/-- Completed equivalence of the ORIGINAL residue and actual local-family
clauses. The prime-classification/existence direction is a separate gap. -/
theorem refined_pattern_iff_local_families (hodd : p≠2) :
    RefinedPattern p ↔ ∀ s : ℕ,1≤s→(PaperRefinedPairs p s).Infinite := by
  exact ⟨fun h s hs=>refined_pattern_infinite_pairs hodd h s hs,
    fun h=>(paper_refined_infinite_reverse hodd h).1⟩

end FourCorner.CriticalRefinedCompletion
#print axioms FourCorner.CriticalRefinedCompletion.refined_pattern_infinite_pairs
#print axioms FourCorner.CriticalRefinedCompletion.refined_pattern_infinite_triples
#print axioms FourCorner.CriticalRefinedCompletion.paper_refined_local_reverse
#print axioms FourCorner.CriticalRefinedCompletion.paper_refined_infinite_reverse
#print axioms FourCorner.CriticalRefinedCompletion.refined_pattern_iff_local_families
