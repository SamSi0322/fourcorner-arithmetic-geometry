import CriticalCRTCompletion
import CriticalPaperReverse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FourCorner
open CriticalPadicConverse
variable {p : ℕ} [Fact p.Prime]

theorem critical_allowed_iff_unit_pattern (hmod : p % 4 = 1) :
    (p ≠ 5 ∧ p ≠ 13) ↔ UnitCriticalSquarePattern p := by
  constructor
  · rintro ⟨h5,h13⟩
    exact CriticalCRTCompletion.allowed_unit_pattern p hmod h5 h13
  · intro h
    exact critical_pattern_excludes_exceptional (unitCriticalSquarePattern_to_pattern h)

/-- The singleton specialization of the actual simultaneous construction
gives the paper's literal infinite integer-triple clause at EVERY depth. -/
theorem critical_infinite_local_triples (hmod : p % 4 = 1) (h5 : p ≠ 5) (h13 : p ≠ 13) :
    ∀ s : ℕ, 1 ≤ s →
      {t : ℤ × ℤ × ℤ | PaperCriticalLocalTriple p s t.1 t.2.1 t.2.2}.Infinite := by
  intro s hs
  have hp : ∀ q ∈ ({p}:Finset ℕ), q.Prime := by
    intro q hq
    have he := Finset.mem_singleton.mp hq
    subst q
    exact Fact.out
  have hm : ∀ q ∈ ({p}:Finset ℕ), q % 4 = 1 := by simpa using hmod
  have h5' : ∀ q ∈ ({p}:Finset ℕ), q ≠ 5 := by simpa using h5
  have h13' : ∀ q ∈ ({p}:Finset ℕ), q ≠ 13 := by simpa using h13
  have hs' : ∀ q ∈ ({p}:Finset ℕ), 1 ≤ (fun _ : ℕ => s) q := by simpa using hs
  have h := (critical_crt {p} (fun _=>s) hp hm h5' h13' hs').1
  apply h.mono
  intro t ht
  obtain ⟨hX,hY,hXL,hYL,hprim,hlocal⟩ := ht
  exact ⟨hX,hY,hXL,hYL,hprim,hlocal p (Finset.mem_singleton_self p)⟩

theorem critical_unit_iff_infinite_local (hmod : p % 4 = 1) :
    UnitCriticalSquarePattern p ↔
      ∀ s : ℕ, 1 ≤ s →
        {t : ℤ × ℤ × ℤ | PaperCriticalLocalTriple p s t.1 t.2.1 t.2.2}.Infinite := by
  constructor
  · intro h
    obtain ⟨h5,h13⟩ := (critical_allowed_iff_unit_pattern hmod).mpr h
    exact critical_infinite_local_triples hmod h5 h13
  · intro h
    have hodd : p ≠ 2 := by omega
    exact (paper_infinite_local_reverse hodd h).1

/-- Complete thm:crit-basic: all three original clauses are equivalent,
the exceptional patterns are excluded even when zeros are allowed, and the
exceptional-content implication holds in the original primitive model. -/
theorem critical_basic (hmod : p % 4 = 1) :
    ((p ≠ 5 ∧ p ≠ 13) ↔ UnitCriticalSquarePattern p) ∧
    (UnitCriticalSquarePattern p ↔
      ∀ s : ℕ, 1 ≤ s →
        {t : ℤ × ℤ × ℤ | PaperCriticalLocalTriple p s t.1 t.2.1 t.2.2}.Infinite) ∧
    (¬CriticalSquarePattern 5) ∧ (¬CriticalSquarePattern 13) ∧
    (∀ M : IntegralModel, ∀ q : ℕ, q = 5 ∨ q = 13 → q ∣ M.radiusContent →
      (q:ℤ) ∣ M.reducedSide) := by
  exact ⟨critical_allowed_iff_unit_pattern hmod,critical_unit_iff_infinite_local hmod,
    no_critical_pattern_five,no_critical_pattern_thirteen,
    fun M _ hq hG=>M.exceptional_content_dvd_reducedSide hq hG⟩

/-- The final clause also applies to every ORIGINAL strict rational
four-distance point through its actual least-denominator primitive model. -/
theorem critical_basic_original_source {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    ∃ M : IntegralModel,
      M.L = (Nat.lcm x.den y.den : ℤ) ∧
      (M.X:ℚ)/M.L=x ∧ (M.Y:ℚ)/M.L=y ∧
      (M.A₀:ℚ)/M.L=r₀ ∧ (M.A₁:ℚ)/M.L=r₁ ∧
      (M.A₂:ℚ)/M.L=r₂ ∧ (M.A₃:ℚ)/M.L=r₃ ∧
      ∀ q : ℕ, q = 5 ∨ q = 13 → q ∣ M.radiusContent →
        (q:ℤ) ∣ M.reducedSide :=
  strictPoint_exceptional_content h

end FourCorner
#print axioms FourCorner.critical_allowed_iff_unit_pattern
#print axioms FourCorner.critical_infinite_local_triples
#print axioms FourCorner.critical_unit_iff_infinite_local
#print axioms FourCorner.critical_basic
#print axioms FourCorner.critical_basic_original_source
