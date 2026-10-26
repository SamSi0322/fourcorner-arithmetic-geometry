import CrtSupport.CriticalBasicWave24
import CrtSupport.CriticalCRTAssemblyWave25

set_option autoImplicit false
namespace FourCorner
open CriticalCRTWave25

/-- Clause (ii) of `thm:crit-basic` implies clause (iii), with an explicit
injective family of rational coordinate pairs at every unrestricted depth. -/
theorem critical_pattern_all_depth_family {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpat : UnitCriticalSquarePattern p)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ X Y a m : ℕ, 0 < X ∧ 0 < Y ∧ 0 < a ∧ 0 < m ∧
      (∀ k : ℕ, X < denominator a m k ∧ Y < denominator a m k ∧
        Nat.gcd (Nat.gcd X Y) (denominator a m k) = 1 ∧
        padicValNat p (denominator a m k) = 2*s ∧
        ∃ A : Fin 4 → ℚ_[p], ∀ j,
          A j ^ 2 = (criticalRadicands X Y (denominator a m k) j : ℚ_[p]) ∧
          (A j).valuation = (s : ℤ)) ∧
      Function.Injective (fun k : ℕ => ((X : ℚ)/denominator a m k,
        (Y : ℚ)/denominator a m k)) := by
  have hprime : ∀ q ∈ ({p} : Finset ℕ), q.Prime := by
    intro q hq
    have he : q = p := Finset.mem_singleton.mp hq
    subst q
    exact Fact.out
  have hodd : ∀ q ∈ ({p} : Finset ℕ), q ≠ 2 := by
    intro q hq
    exact Finset.mem_singleton.mp hq ▸ hp2
  have hdepth : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ (fun _ : ℕ => s) q := by
    intro q hq
    exact hs
  have hpatterns : ∀ q ∈ ({p} : Finset ℕ), ∃ i b c : ZMod q,
      i^2 = -1 ∧ b ≠ 0 ∧
      (c ≠ 0 ∧ c+b ≠ 0 ∧ c+i*b ≠ 0 ∧ c+(1+i)*b ≠ 0) ∧
      (IsSquare c ∧ IsSquare (c+b) ∧ IsSquare (c+i*b) ∧ IsSquare (c+(1+i)*b)) := by
    intro q hq
    have he : q = p := Finset.mem_singleton.mp hq
    subst q
    obtain ⟨i,b,c,hi,hb,h0,h1,h2,h3,hu⟩ := hpat
    exact ⟨i,b,c,hi,hb,hu,h0,h1,h2,h3⟩
  obtain ⟨X,Y,a,m,hX,hY,ha,hm,hall,hinj⟩ :=
    simultaneous_from_residue_patterns {p} (fun _ => s) hprime hodd hdepth hpatterns
  refine ⟨X,Y,a,m,hX,hY,ha,hm,?_,hinj⟩
  intro k
  obtain ⟨hXi,hYi,hg,hpr⟩ := hall k
  exact ⟨hXi,hYi,hg,hpr p (Finset.mem_singleton_self p)⟩
end FourCorner
#print axioms FourCorner.critical_pattern_all_depth_family
