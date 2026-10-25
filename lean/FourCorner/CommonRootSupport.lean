import FourCorner.CommonRootSupportParity
import FourCorner.CommonRootSupportDecomposition
import FourCorner.CommonRootMap

namespace FourCorner.CommonRootSource

/-- Odd valuation of the common coordinate can occur only at positive odd
valuation of the discriminant, for the actual rational four-root source. -/
theorem rational_odd_support {t : ℚ} (S : CommonRootSource ℚ t) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hodd : Odd (padicValRat p S.ell)) :
    0 < padicValRat p (t^2-1) ∧ Odd (padicValRat p (t^2-1)) := by
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd (S.toPadic p).ell.valuation := by
    simpa only [toPadic_ell, Padic.valuation_ratCast] using hodd
  have h := (S.toPadic p).support_val_d_pos_odd_of_ell_odd hp2 ho
  have he : (t : ℚ_[p])^2-1 = ((t^2-1 : ℚ) : ℚ_[p]) := by push_cast; rfl
  rw [he,Padic.valuation_ratCast] at h
  exact h

/-- Lemma lem:common-support in an explicit finite-generator form.
The common coordinate is a sign, an allowed prime product, and a rational square. -/
theorem squareclass_support {t : ℚ} (S : CommonRootSource ℚ t) :
    ∃ F : Finset ℕ,
      (∀ p ∈ F, p.Prime ∧ (p=2 ∨
        (0 < padicValRat p (t^2-1) ∧ Odd (padicValRat p (t^2-1))))) ∧
      ∃ ε u : ℚ, (ε=1 ∨ ε= -1) ∧ 0<u ∧
        S.ell = ε * (∏ p ∈ F, (p : ℚ)) * u^2 := by
  apply FourCorner.rat_prime_product_support_decomposition S.ell_ne_zero
  intro p hp hp2 hodd
  exact S.rational_odd_support hp hp2 hodd

/-- The rational common coordinate is positive throughout the parameter range t>1. -/
theorem ell_pos_of_one_lt {t : ℚ} (S : CommonRootSource ℚ t) (ht : 1<t) :
    0 < S.ell := by
  have hc := S.sqC
  nlinarith [sq_nonneg S.C]

/-- The positive squarefree representative and its complete prime support,
with no sign generator needed when t>1. -/
theorem positive_squareclass_support {t : ℚ} (S : CommonRootSource ℚ t) (ht : 1<t) :
    ∃ n : ℕ, 0<n ∧ Squarefree n ∧
      (∀ p : ℕ, p.Prime → p∣n → p=2 ∨
        (0 < padicValRat p (t^2-1) ∧ Odd (padicValRat p (t^2-1)))) ∧
      ∃ u : ℚ, 0<u ∧ S.ell=(n : ℚ)*u^2 := by
  apply FourCorner.positive_rat_squarefree_support_decomposition (S.ell_pos_of_one_lt ht)
  intro p hp hp2 hodd
  exact S.rational_odd_support hp hp2 hodd

end FourCorner.CommonRootSource
#print axioms FourCorner.CommonRootSource.rational_odd_support
#print axioms FourCorner.CommonRootSource.squareclass_support
#print axioms FourCorner.CommonRootSource.positive_squareclass_support
