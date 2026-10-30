import CrtSupport.CriticalBasicLiftWave24
import CrtSupport.CriticalCRTWave25

set_option autoImplicit false
namespace FourCorner.CriticalCRTWave25

/-- A congruence one digit beyond twice the desired root depth preserves
actual roots in the completed field and their exact valuations. -/
theorem roots_persist_at_depth {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (s : ℕ) (Q Q' q : Fin 4 → ℤ)
    (hfac : ∀ j, Q j = (p : ℤ)^(2*s)*q j)
    (hu : ∀ j, ¬(p : ℤ) ∣ q j)
    (hs : ∀ j, IsSquare (q j : ZMod p))
    (hcong : ∀ j, (p : ℤ)^(2*s+1) ∣ Q' j-Q j) :
    ∃ A : Fin 4 → ℚ_[p], ∀ j,
      A j ^ 2 = (Q' j : ℚ_[p]) ∧ (A j).valuation = (s : ℤ) := by
  choose z hz using hcong
  let q' : Fin 4 → ℤ := fun j => q j + p*z j
  have hres (j : Fin 4) : (q' j : ZMod p) = (q j : ZMod p) := by
    simp [q']
  apply critical_four_scaled_roots hp s Q' q'
  · intro j
    have he := hz j
    rw [pow_succ, hfac j] at he
    dsimp [q']
    linear_combination he
  · intro j hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (q' j) p).mpr hd
    rw [hres] at hz
    exact hu j ((ZMod.intCast_zmod_eq_zero_iff_dvd (q j) p).mp hz)
  · intro j
    rw [hres]
    exact hs j

/-- The four original distance polynomials retain the required precision
when just the denominator changes by a multiple of the local modulus. -/
theorem radicands_congruent_denominator (X Y L L' m : ℤ)
    (h : m ∣ L'-L) :
    ∀ j : Fin 4, m ∣ criticalRadicands X Y L' j - criticalRadicands X Y L j := by
  obtain ⟨z,hz⟩ := h
  have he : L' = L + m*z := by omega
  rw [he]
  intro j
  fin_cases j
  · simp [criticalRadicands]
  · refine ⟨-2*X*z+2*L*z+m*z^2, ?_⟩
    simp [criticalRadicands]
    ring
  · refine ⟨-2*Y*z+2*L*z+m*z^2, ?_⟩
    simp [criticalRadicands]
    ring
  · refine ⟨-2*X*z-2*Y*z+4*L*z+2*m*z^2, ?_⟩
    simp [criticalRadicands]
    ring

/-- Persistence applies directly to the actual four original radicands,
with a single denominator congruence and an unrestricted depth. -/
theorem original_roots_persist {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (s : ℕ) (X Y L L' : ℤ) (q : Fin 4 → ℤ)
    (hfac : ∀ j, criticalRadicands X Y L j = (p : ℤ)^(2*s)*q j)
    (hu : ∀ j, ¬(p : ℤ) ∣ q j)
    (hs : ∀ j, IsSquare (q j : ZMod p))
    (hcong : (p : ℤ)^(2*s+1) ∣ L'-L) :
    ∃ A : Fin 4 → ℚ_[p], ∀ j,
      A j ^ 2 = (criticalRadicands X Y L' j : ℚ_[p]) ∧
      (A j).valuation = (s : ℤ) := by
  exact roots_persist_at_depth hp s _ _ q hfac hu hs
    (radicands_congruent_denominator X Y L L' _ hcong)

end FourCorner.CriticalCRTWave25
#print axioms FourCorner.CriticalCRTWave25.original_roots_persist
