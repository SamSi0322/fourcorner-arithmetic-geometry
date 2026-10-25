import FourCorner.CommonRootReturn
import FourCorner.CommonRootDyadicNormalize
import FourCorner.CommonRootDyadicProducts
import FourCorner.CommonRootDyadicSquareD

namespace FourCorner.CommonRootSource

/-- The full dyadic valuation dichotomy for every actual ordered source. -/
theorem dyadic_valuation_alternatives {t : ℚ_[2]} (S : CommonRootSource ℚ_[2] t) :
    2 ≤ t.valuation ∨ (t.valuation < 0 ∧ Odd t.valuation) := by
  obtain ⟨h0,h1,h2,h3⟩ := S.return_four_squares
  have hf := commonRoot_dyadic_frame_of_four_squares
    S.returnX S.returnY S.returnR0 S.returnR1 S.returnR2 S.returnR3 h0 h1 h2 h3
  rw [S.return_opposite_product] at hf
  obtain ⟨F⟩ := hf
  exact F.classification S.t_ne_zero

/-- A square value of t²−1 forces the negative odd branch and exactly the
same valuation of the common coordinate; no height or depth bound is imposed. -/
theorem dyadic_square_d_valuation {t : ℚ_[2]} (S : CommonRootSource ℚ_[2] t)
    (hd : IsSquare (t^2-1)) :
    S.ell.valuation = t.valuation ∧ t.valuation < 0 ∧ Odd t.valuation := by
  rcases S.dyadic_valuation_alternatives with hpos | ⟨hneg,hodd⟩
  · exact False.elim (commonRoot_dyadic_d_nonsquare_of_val_ge_two t hpos hd)
  · exact ⟨S.dyadic_ell_val_eq_of_negative_odd hneg hodd,hneg,hodd⟩

/-- Complete Lemma common-dyadic on the actual completed field Q2. -/
theorem common_dyadic {t : ℚ_[2]} (S : CommonRootSource ℚ_[2] t) :
    (2 ≤ t.valuation ∨ (t.valuation < 0 ∧ Odd t.valuation)) ∧
    (IsSquare (t^2-1) →
      S.ell.valuation = t.valuation ∧ t.valuation < 0 ∧ Odd t.valuation) :=
  ⟨S.dyadic_valuation_alternatives,S.dyadic_square_d_valuation⟩

#print axioms dyadic_valuation_alternatives
#print axioms dyadic_square_d_valuation
#print axioms common_dyadic
end FourCorner.CommonRootSource
