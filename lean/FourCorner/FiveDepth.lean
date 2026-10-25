import FourCorner.DenominatorBoundsCorollary
import FourCorner.PairDenominators
import FourCorner.FiveNoncritical
import FourCorner.FiveSignedDepth
import FourCorner.FiveGrowth

namespace FourCorner
namespace IntegralModel

/-- The cofactor after the complete power of five in the least denominator
has been removed. This is an integer, not a bounded truncation. -/
def fiveCofactor (M : IntegralModel) : ℤ := M.L / (5 : ℤ)^padicValInt 5 M.L

theorem fiveCofactor_pos (M : IntegralModel) : 0 < M.fiveCofactor :=
  Int.ediv_pos_of_pos_of_dvd M.L_pos (le_of_lt (pow_pos (by norm_num) _))
    (padicValInt_dvd M.L)

theorem fiveCofactor_factorization (M : IntegralModel) :
    (5 : ℤ)^padicValInt 5 M.L * M.fiveCofactor = M.L :=
  Int.mul_ediv_cancel' (padicValInt_dvd M.L)

theorem fiveCofactor_not_dvd (M : IntegralModel) : ¬ (5 : ℤ) ∣ M.fiveCofactor := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  have hh : (5 : ℤ)^(padicValInt 5 M.L + 1) ∣ M.L := by
    have ht := mul_dvd_mul_left ((5 : ℤ)^padicValInt 5 M.L) hd
    rwa [← pow_succ, M.fiveCofactor_factorization] at ht
  have hv := (padicValInt_dvd_iff (p := 5) (padicValInt 5 M.L + 1) M.L).mp hh
  rcases hv with hz | hv
  · exact (ne_of_gt M.L_pos) hz
  · omega

/-- Proposition prop:int:five-depth. The exponent in the strict growth
inequality is an integer exponent; it is not truncated at zero. -/
theorem five_depth (M : IntegralModel) (hL : (5 : ℤ) ∣ M.L)
    (hXY : ¬ (5 : ℤ) ∣ M.X * M.Y) :
    ∃ s : ℕ, 1 ≤ s ∧
      (∀ i : Fin 4, padicValInt 5 (M.pairRadius i) = s) ∧
      2*s < padicValInt 5 M.L ∧
      (∃ b c d : ℤ,
        (b=M.A₁ ∨ b= -M.A₁) ∧ (c=M.A₂ ∨ c= -M.A₂) ∧
        (d=M.A₃ ∨ d= -M.A₃) ∧ M.A₀-b-c+d ≠ 0 ∧
        padicValInt 5 (M.A₀-b-c+d) = 2*padicValInt 5 M.L-3*s) ∧
      (5 : ℝ)^((padicValInt 5 M.L : ℤ)-3*(s : ℤ)) <
        (2+Real.sqrt 2)/2*(M.fiveCofactor : ℝ) := by
  obtain ⟨hs,hdeep,h₀,h₁,h₂,h₃⟩ := M.five_noncritical hL hXY
  obtain ⟨b,c,d,hb,hc,hd,hne,hv⟩ := M.five_signed_value
    (padicValInt 5 (M.radiusContent : ℤ)) h₀ h₁ h₂ h₃ hXY hdeep
  refine ⟨padicValInt 5 (M.radiusContent : ℤ),hs,?_,hdeep,
    ⟨b,c,d,hb,hc,hd,hne,hv⟩,?_⟩
  · intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
  · exact M.five_growth_of_signed_depth hdeep hb hc hd hne hv

end IntegralModel
end FourCorner
#print axioms FourCorner.IntegralModel.fiveCofactor_not_dvd

#print axioms FourCorner.IntegralModel.five_depth
