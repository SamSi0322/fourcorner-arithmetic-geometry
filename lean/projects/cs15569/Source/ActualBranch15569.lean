import HSupport15569
import ActualPairData

/-! The unique strict-real surviving order for the same actual U,V.
An ActualPair includes an actual H/torsion decomposition; constructing that
from every raw source still requires the missing E(Q)=H⊕E[2] splitting. -/
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section

/-- Both surviving orders came from the actual even-valuation dyadic test.
Global support on the entire actual H eliminates the second order over R. -/
theorem actual_pair_unique_branch (S : ActualPair 15569 (by norm_num))
    (r : S.Remainders) :
    S.a=commonSourceTranslateMinus (15569 : ℚ) r.x ∧
      S.c=commonSourceTranslatePlus (15569 : ℚ) r.w := by
  have hxv := (some_mem_H_iff 15569 (by norm_num) r.x r.y
    (nonsingular (by norm_num) r.hU)).mp r.memU
  have hreal := depth_two_real_identity r.hU hxv
  have ho := r.surviving_orders (Or.inl (by norm_num))
  rcases ho with ⟨_,ho⟩ | ⟨hwrong,_⟩
  · rcases ho with ho | ho
    · exact ho
    · have hpos : 0 < S.a := by
        rw [ho.1]
        unfold commonSourceTranslatePlus
        have hden : 0 < r.x-15569 := by linarith
        positivity
      linarith [S.ha]
  · norm_num at hwrong

#print axioms actual_pair_unique_branch
end
end FourCorner.Cs15569Completion
