import CrtSupport.CriticalBasicFamilyWave24

set_option autoImplicit false
namespace FourCorner
open CriticalCRTWave25

/-- A primitive positive interior integer triple with the prescribed exact
local denominator depths and actual roots of the four original radicands. -/
def CriticalCRTRealization (P : Finset ℕ) (s : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (X Y L : ℤ) : Prop :=
  0 < X ∧ 0 < Y ∧ X < L ∧ Y < L ∧ Int.gcd (Int.gcd X Y : ℤ) L = 1 ∧
    ∀ p (h : p ∈ P),
      letI : Fact p.Prime := ⟨hp p h⟩
      padicValInt p L = 2*s p ∧
      ∃ A : Fin 4 → ℚ_[p], ∀ j,
        A j ^ 2 = (criticalRadicands X Y L j : ℚ_[p]) ∧
        (A j).valuation = (s p : ℤ)

/-- The CRT family has infinitely many actual primitive integer triples
and infinitely many actual rational pairs. This support theorem isolates
only the already proved local pattern input, which must be discharged by
the unconditional prime classification before counting the corollary. -/
theorem critical_crt_infinite_from_unit_patterns (P : Finset ℕ) (s : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, p ≠ 2)
    (hspos : ∀ p ∈ P, 1 ≤ s p)
    (hpat : ∀ p ∈ P, UnitCriticalSquarePattern p) :
    {t : ℤ × ℤ × ℤ | CriticalCRTRealization P s hp t.1 t.2.1 t.2.2}.Infinite ∧
    {z : ℚ × ℚ | ∃ X Y L : ℤ, CriticalCRTRealization P s hp X Y L ∧
      z = ((X : ℚ)/L, (Y : ℚ)/L)}.Infinite := by
  have hpatterns : ∀ p ∈ P, ∃ i b c : ZMod p, i^2 = -1 ∧ b ≠ 0 ∧
      (c ≠ 0 ∧ c+b ≠ 0 ∧ c+i*b ≠ 0 ∧ c+(1+i)*b ≠ 0) ∧
      (IsSquare c ∧ IsSquare (c+b) ∧ IsSquare (c+i*b) ∧ IsSquare (c+(1+i)*b)) := by
    intro p h
    obtain ⟨i,b,c,hi,hb,h0,h1,h2,h3,hu⟩ := hpat p h
    exact ⟨i,b,c,hi,hb,hu,h0,h1,h2,h3⟩
  obtain ⟨X,Y,a,m,hX,hY,ha,hm,hall,hinj⟩ :=
    simultaneous_from_residue_patterns P s hp hodd hspos hpatterns
  have hr (k : ℕ) : CriticalCRTRealization P s hp X Y (denominator a m k) := by
    obtain ⟨hXL,hYL,hg,hlocal⟩ := hall k
    obtain ⟨hXz,hYz,hXLz,hYLz,hgz⟩ := integer_primitive_interior X Y _ hX hY hXL hYL hg
    refine ⟨hXz,hYz,hXLz,hYLz,hgz,?_⟩
    intro p h
    letI : Fact p.Prime := ⟨hp p h⟩
    obtain ⟨hv,hA⟩ := hlocal p h
    exact ⟨by simpa only [padicValInt, Int.natAbs_natCast] using hv,hA⟩
  constructor
  · have hinjt : Function.Injective (fun k : ℕ => ((X : ℤ),(Y : ℤ),(denominator a m k : ℤ))) := by
      intro j k he
      apply denominator_injective a m hm
      have hz := congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) he
      change (denominator a m j : ℤ) = denominator a m k at hz
      exact_mod_cast hz
    apply (Set.infinite_range_of_injective hinjt).mono
    rintro _ ⟨k,rfl⟩
    exact hr k
  · apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨k,rfl⟩
    exact ⟨X,Y,denominator a m k,hr k,rfl⟩

end FourCorner
#print axioms FourCorner.critical_crt_infinite_from_unit_patterns
