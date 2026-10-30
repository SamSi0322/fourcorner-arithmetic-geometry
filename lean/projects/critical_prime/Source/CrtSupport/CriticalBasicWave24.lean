import FourCorner.CriticalExcessActual
import FourCorner.IntegralNormalization

set_option autoImplicit false
namespace FourCorner

/-- The actual residue pattern; zero square entries are permitted. -/
def CriticalSquarePattern (p : ℕ) : Prop :=
  ∃ i b c : ZMod p, i ^ 2 = -1 ∧ b ≠ 0 ∧
    IsSquare c ∧ IsSquare (c+b) ∧ IsSquare (c+i*b) ∧
    IsSquare (c+(1+i)*b)

/-- Exhaustion includes both roots of minus one and every square class of the shift. -/
theorem no_critical_pattern_five : ¬ CriticalSquarePattern 5 := by
  unfold CriticalSquarePattern
  decide

theorem no_critical_pattern_thirteen : ¬ CriticalSquarePattern 13 := by
  unfold CriticalSquarePattern
  decide

/-- The open residue pattern used in the existence clause. -/
def UnitCriticalSquarePattern (p : ℕ) : Prop :=
  ∃ i b c : ZMod p, i ^ 2 = -1 ∧ b ≠ 0 ∧
    IsSquare c ∧ IsSquare (c+b) ∧ IsSquare (c+i*b) ∧
    IsSquare (c+(1+i)*b) ∧ c ≠ 0 ∧ c+b ≠ 0 ∧
    c+i*b ≠ 0 ∧ c+(1+i)*b ≠ 0

theorem critical_unit_pattern_seventeen : UnitCriticalSquarePattern 17 := by
  refine ⟨4, 3, 1, ?_, ?_, ⟨1, ?_⟩, ⟨2, ?_⟩, ⟨8, ?_⟩, ⟨4, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> decide

theorem critical_unit_pattern_twentyNine : UnitCriticalSquarePattern 29 := by
  refine ⟨12, 2, 4, ?_, ?_, ⟨2, ?_⟩, ⟨8, ?_⟩, ⟨12, ?_⟩, ⟨1, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> decide

/-- All allowed primes below the Hasse-bound range are accounted for. -/
theorem critical_unit_pattern_small {p : ℕ} (hp : p.Prime)
    (hmod : p % 4 = 1) (h5 : p ≠ 5) (h13 : p ≠ 13) (hlt : p < 37) :
    UnitCriticalSquarePattern p := by
  interval_cases p <;> first
    | exact critical_unit_pattern_seventeen
    | exact critical_unit_pattern_twentyNine
    | (exfalso; exact (by decide : ¬ Nat.Prime _) hp)
    | omega

theorem unitCriticalSquarePattern_to_pattern {p : ℕ}
    (h : UnitCriticalSquarePattern p) : CriticalSquarePattern p := by
  obtain ⟨i,b,c,hi,hb,h0,h1,h2,h3,_⟩ := h
  exact ⟨i,b,c,hi,hb,h0,h1,h2,h3⟩

/-- The exclusion implication in the prime classification. -/
theorem critical_pattern_excludes_exceptional {p : ℕ} (h : CriticalSquarePattern p) :
    p ≠ 5 ∧ p ≠ 13 := by
  constructor
  · intro he
    subst p
    exact no_critical_pattern_five h
  · intro he
    subst p
    exact no_critical_pattern_thirteen h

namespace IntegralModel
/-- At each exceptional prime, actual radius content forces additional side content. -/
theorem exceptional_content_dvd_reducedSide (M : IntegralModel) {p : ℕ}
    (hp : p = 5 ∨ p = 13) (hG : p ∣ M.radiusContent) :
    (p : ℤ) ∣ M.reducedSide := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  letI : Fact p.Prime := ⟨hprime⟩
  by_contra hH
  obtain ⟨hi,hb,h1,h2,h3⟩ := M.content_prime_square_pattern hG hH
  have hpat : CriticalSquarePattern p := by
    refine ⟨M.contentPrimeIota p, M.contentPrimeShift p,
      (M.criticalReducedRadius 0 : ZMod p)^2, hi, hb, ?_, ?_, ?_, ?_⟩
    · exact ⟨_, by ring⟩
    · exact ⟨(M.criticalReducedRadius 1 : ZMod p), by rw [← h1]; ring⟩
    · exact ⟨(M.criticalReducedRadius 2 : ZMod p), by rw [← h2]; ring⟩
    · exact ⟨(M.criticalReducedRadius 3 : ZMod p), by rw [← h3]; ring⟩
  rcases hp with rfl | rfl
  · exact no_critical_pattern_five hpat
  · exact no_critical_pattern_thirteen hpat
end IntegralModel
/-- The exceptional-content conclusion on the actual least-denominator
primitive normalization of every original rational four-distance point. -/
theorem strictPoint_exceptional_content {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    ∃ M : IntegralModel,
      M.L = (Nat.lcm x.den y.den : ℤ) ∧
      (M.X : ℚ)/M.L = x ∧ (M.Y : ℚ)/M.L = y ∧
      (M.A₀ : ℚ)/M.L = r₀ ∧ (M.A₁ : ℚ)/M.L = r₁ ∧
      (M.A₂ : ℚ)/M.L = r₂ ∧ (M.A₃ : ℚ)/M.L = r₃ ∧
      ∀ p : ℕ, p = 5 ∨ p = 13 → p ∣ M.radiusContent →
        (p : ℤ) ∣ M.reducedSide := by
  obtain ⟨M,hL,hX,hY,h0,h1,h2,h3⟩ := strictPoint_iff_primitiveIntegral.mp h
  exact ⟨M,hL,hX,hY,h0,h1,h2,h3,fun _ hp hg => M.exceptional_content_dvd_reducedSide hp hg⟩
end FourCorner
#print axioms FourCorner.no_critical_pattern_five
#print axioms FourCorner.no_critical_pattern_thirteen
#print axioms FourCorner.IntegralModel.exceptional_content_dvd_reducedSide

#print axioms FourCorner.critical_unit_pattern_seventeen
#print axioms FourCorner.critical_unit_pattern_twentyNine

#print axioms FourCorner.strictPoint_exceptional_content

#print axioms FourCorner.critical_unit_pattern_small

#print axioms FourCorner.critical_pattern_excludes_exceptional
