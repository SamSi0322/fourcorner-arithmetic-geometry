import CriticalResiduePatternData
import CrtSupport.CriticalBasicWave24

noncomputable section
namespace FourCorner.CriticalPadicConverse
open CriticalNormalizedRadii CriticalResiduePatternData
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 1500000

/-- TRUE local reverse: the original SAME tuple of completed-field radii,
at any positive depth, yields the original literal UNIT critical pattern.
No rational/integer radii or global four-distance point are substituted. -/
theorem unit_pattern_of_padic_roots (hodd : p≠2) (X Y L : ℤ) (s : ℕ) (hs : 1≤s)
    (A : Fin 4 → ℚ_[p])
    (hprim : Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs=1)
    (hroot : Equations X Y L A) (hL : padicValInt p L=2*s)
    (hA : ∀ j,(A j).valuation=(s:ℤ)) : UnitCriticalSquarePattern p := by
  have hLQ : (L:ℚ_[p]).valuation=((2*s:ℕ):ℤ) := by rw [Padic.valuation_intCast,hL]
  let D:=normalized_data X Y L s hs A hroot hLQ hA
  obtain ⟨hx,hy,hi,hb,hr,h1,h2,h3⟩:=pattern_data hodd X Y L s hs A hprim hroot hLQ hA
  refine ⟨iota (p:=p) X Y,step D,(radius D 0)^2,hi,hb,
    ⟨radius D 0,by ring⟩,⟨radius D 1,?_⟩,⟨radius D 2,?_⟩,⟨radius D 3,?_⟩,
    pow_ne_zero 2 (hr 0),?_,?_,?_⟩
  · rw [←h1];ring
  · rw [←h2];ring
  · rw [←h3];ring
  · rw [←h1];exact pow_ne_zero 2 (hr 1)
  · rw [←h2];exact pow_ne_zero 2 (hr 2)
  · rw [←h3];exact pow_ne_zero 2 (hr 3)

/-- Both exceptional primes are impossible for these actual local inputs,
including all positive depths and every choice of the four root signs. -/
theorem padic_roots_exclude_exceptional (hodd : p≠2) (X Y L : ℤ) (s : ℕ) (hs : 1≤s)
    (A : Fin 4 → ℚ_[p])
    (hprim : Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs=1)
    (hroot : Equations X Y L A) (hL : padicValInt p L=2*s)
    (hA : ∀ j,(A j).valuation=(s:ℤ)) : p≠5 ∧ p≠13 :=
  critical_pattern_excludes_exceptional (unitCriticalSquarePattern_to_pattern
    (unit_pattern_of_padic_roots hodd X Y L s hs A hprim hroot hL hA))
end FourCorner.CriticalPadicConverse
#print axioms FourCorner.CriticalPadicConverse.unit_pattern_of_padic_roots
#print axioms FourCorner.CriticalPadicConverse.padic_roots_exclude_exceptional
