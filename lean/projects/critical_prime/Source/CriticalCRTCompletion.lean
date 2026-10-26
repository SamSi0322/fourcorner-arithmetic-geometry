import CriticalCRTInterfaces
import CriticalCRTPrimeBridge

set_option autoImplicit false
namespace FourCorner

/-- Manuscript cor:crit-crt, with literal primitive integer triples and
actual completed-field roots of the four original radicands. The second
conclusion records infinitely many distinct actual rational coordinate
pairs as well. The finite prime set may be empty and the depths arbitrary. -/
theorem critical_crt (P : Finset ℕ) (s : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hmod : ∀ p ∈ P, p % 4 = 1)
    (h5 : ∀ p ∈ P, p ≠ 5) (h13 : ∀ p ∈ P, p ≠ 13)
    (hspos : ∀ p ∈ P, 1 ≤ s p) :
    {t : ℤ × ℤ × ℤ | CriticalCRTRealization P s hp t.1 t.2.1 t.2.2}.Infinite ∧
    {z : ℚ × ℚ | ∃ X Y L : ℤ, CriticalCRTRealization P s hp X Y L ∧
      z = ((X : ℚ)/L, (Y : ℚ)/L)}.Infinite := by
  have hodd : ∀ p ∈ P, p ≠ 2 := by
    intro p h
    have hm := hmod p h
    omega
  apply critical_crt_infinite_from_unit_patterns P s hp hodd hspos
  intro p h
  letI : Fact p.Prime := ⟨hp p h⟩
  exact CriticalCRTCompletion.allowed_unit_pattern p (hmod p h) (h5 p h) (h13 p h)

end FourCorner
#print axioms FourCorner.critical_crt
