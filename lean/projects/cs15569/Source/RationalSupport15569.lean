import CS15569Support.NineSmallASignedSupport
import FourCorner.OrderedSourceAlgebra
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Actual global Kummer support for the literal curve E_15569.
This module proves a descent prerequisite, not thm:cs-15569. All statements
quantify over arbitrary rational points, including denominator primes.
The slots remain in the paper's order x, x-15569, x+15569. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace FourCorner.Cs15569Completion

/-- The sign and every possible prime factor of a squareclass are explicit. -/
def SupportedClass (q : ℚ) : Prop :=
  ∃ d : ℤ, (d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 ∨
    d = 15569 ∨ d = -15569 ∨ d = 31138 ∨ d = -31138) ∧
    ∃ u : ℚ, 0 < u ∧ q = (d : ℚ) * u^2

/-- The first slot has the stronger support {-1,15569}. -/
def FirstSupportedClass (q : ℚ) : Prop :=
  ∃ d : ℤ, (d = 1 ∨ d = -1 ∨ d = 15569 ∨ d = -15569) ∧
    ∃ u : ℚ, 0 < u ∧ q = (d : ℚ) * u^2

private theorem signed_divisor_n {d : ℤ} (hs : Squarefree d.natAbs)
    (hd : d ∣ -(15569 : ℤ)^2) :
    d = 1 ∨ d = -1 ∨ d = 15569 ∨ d = -15569 := by
  have hh : d.natAbs ∣ 15569^2 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hd
  have hn : d.natAbs ∣ 15569 := (hs.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hh
  have hm := Nat.mem_divisors.mpr ⟨hn, (by norm_num : 15569 ≠ 0)⟩
  have hl : Nat.divisors 15569 = {1,15569} := by decide
  rw [hl] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm <;> rcases Int.natAbs_eq_iff.mp hm with h | h <;> simp_all

private theorem signed_divisor_2n {d : ℤ} (hs : Squarefree d.natAbs)
    (hd : d ∣ 2*(15569 : ℤ)^2) :
    d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 ∨
      d = 15569 ∨ d = -15569 ∨ d = 31138 ∨ d = -31138 := by
  have hh : d.natAbs ∣ 31138^2 := by
    have hd' : d ∣ (31138 : ℤ)^2 := dvd_trans hd (by norm_num)
    simpa using Int.natAbs_dvd_natAbs.mpr hd'
  have hn : d.natAbs ∣ 31138 := (hs.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hh
  have hm := Nat.mem_divisors.mpr ⟨hn, (by norm_num : 31138 ≠ 0)⟩
  have hl : Nat.divisors 31138 = {1,2,15569,31138} := by decide
  rw [hl] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm | hm | hm <;>
    rcases Int.natAbs_eq_iff.mp hm with h | h <;> simp_all

/-- Entire first rational Kummer slot, with no height or integrality restriction. -/
theorem first_support {x y : ℚ} (hx : x ≠ 0)
    (h : y^2 = x*(x-15569)*(x+15569)) : FirstSupportedClass x := by
  have hc : y^2 = x^3 + ((0 : ℤ) : ℚ)*x^2 + ((-(15569 : ℤ)^2) : ℚ)*x := by
    rw [h]; norm_num; ring
  obtain ⟨d,hs,hd,u,hu,he⟩ := cubic_signed_squarefree_support (by norm_num) hx hc
  exact ⟨d,signed_divisor_n hs hd,u,hu,he⟩

/-- Entire second rational Kummer slot after translating the root +15569. -/
theorem minus_support {x y : ℚ} (hx : x-15569 ≠ 0)
    (h : y^2 = x*(x-15569)*(x+15569)) : SupportedClass (x-15569) := by
  have hc : y^2 = (x-15569)^3 + ((3*15569 : ℤ) : ℚ)*(x-15569)^2 +
      ((2*15569^2 : ℤ) : ℚ)*(x-15569) := by rw [h]; norm_num; ring
  obtain ⟨d,hs,hd,u,hu,he⟩ := cubic_signed_squarefree_support (by norm_num) hx hc
  exact ⟨d,signed_divisor_2n hs hd,u,hu,he⟩

/-- Entire third rational Kummer slot after translating the root -15569. -/
theorem plus_support {x y : ℚ} (hx : x+15569 ≠ 0)
    (h : y^2 = x*(x-15569)*(x+15569)) : SupportedClass (x+15569) := by
  have hc : y^2 = (x+15569)^3 + ((-3*15569 : ℤ) : ℚ)*(x+15569)^2 +
      ((2*15569^2 : ℤ) : ℚ)*(x+15569) := by rw [h]; norm_num; ring
  obtain ⟨d,hs,hd,u,hu,he⟩ := cubic_signed_squarefree_support (by norm_num) hx hc
  exact ⟨d,signed_divisor_2n hs hd,u,hu,he⟩

/-- Same actual two finite source points and their ordered slots. The strict
intervals automatically remove all exceptional roots. -/
theorem ordered_source_support {a b c e : ℚ}
    (ha : -(15569 : ℚ) < a) (ha0 : a < 0) (hc : 15569 < c)
    (hQ : b^2 = a*(a-15569)*(a+15569))
    (hR : e^2 = c*(c-15569)*(c+15569)) :
    FirstSupportedClass a ∧ SupportedClass (a-15569) ∧ SupportedClass (a+15569) ∧
    FirstSupportedClass c ∧ SupportedClass (c-15569) ∧ SupportedClass (c+15569) := by
  exact ⟨first_support (by linarith) hQ, minus_support (by linarith) hQ,
    plus_support (by linarith) hQ, first_support (by linarith) hR,
    minus_support (by linarith) hR, plus_support (by linarith) hR⟩

#print axioms first_support
#print axioms minus_support
#print axioms plus_support
#print axioms ordered_source_support

end FourCorner.Cs15569Completion
