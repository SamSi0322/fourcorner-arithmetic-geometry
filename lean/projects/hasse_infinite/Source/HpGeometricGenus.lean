import HpBranchPlaces
import CommonRamificationSum

namespace FourCorner.HpGeometricGenus

open AlgebraicCurve HpLiteralField HpFieldGeometry HpBranchPlaces
noncomputable section
variable (K : Type*) [Field K] [IsAlgClosed K] [NeZero (2 : K)]
attribute [local instance] Classical.propDecidable

theorem actual_index_formula (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (w : Place K (field K p)) :
    w.ramificationIndex (RatFunc K)=if w.restrict (RatFunc K)∈support K p then 2 else 1 := by
  classical
  rw [HpFieldGeometry.index_formula K p hp ha hb]
  have hodd := exists_odd_iff_mem_support K p hp ha hb (w.restrict (RatFunc K))
  by_cases h : w.restrict (RatFunc K)∈support K p
  · rw [if_pos h,if_neg]
    intro hall
    obtain ⟨i,hi⟩ := hodd.mpr h
    exact (Int.not_even_iff_odd.mpr hi) (hall i)
  · rw [if_neg h,if_pos]
    intro i
    by_contra hi
    exact h (hodd.mp ⟨i,Int.not_even_iff_odd.mp hi⟩)

/-- The actual five branch fibers, each of eight places and index two,
give exactly forty in the Riemann–Hurwitz ramification sum. -/
theorem actual_ramification_sum (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    (∑ᶠ w : Place K (field K p),((w.ramificationIndex (RatFunc K) : ℤ)-1))=40 := by
  classical
  letI : PerfectField K := IsAlgClosed.perfectField K
  letI := finite_over_line K p
  letI := separable K p
  letI : IsCurveOver K (RatFunc K) := RatFuncFiniteExtension.isCurveOver_of_perfectField K (RatFunc K)
  letI : IsCurveOver K (field K p) := isCurveOver K p
  let B := support K p
  let S := B.biUnion (fun v => v.fiberOver (field K p))
  have hmem (w : Place K (field K p)) : w∈S ↔ w.restrict (RatFunc K)∈B := by
    simp only [S,Finset.mem_biUnion,Place.mem_fiberOver]
    constructor
    · rintro ⟨v,hv,hw⟩
      exact hw.symm ▸ hv
    · intro hw
      exact ⟨w.restrict (RatFunc K),hw,rfl⟩
  have hcard (v : Place K (RatFunc K)) (hv : v∈B) : (v.fiberOver (field K p)).card=8 := by
    apply CommonRamificationSum.card_fiberOver_eq_eight (field_degree_sixteen K p hp ha hb) v
    · intro w hw
      rw [actual_index_formula K p hp ha hb w,v.restrict_eq_of_mem_fiberOver hw,if_pos hv]
    · intro w _
      exact CommonRamificationSum.inertiaDeg_eq_one w
  have hScard : S.card=40 := by
    dsimp [S]
    rw [Finset.card_biUnion (CommonRamificationSum.fibers_pairwiseDisjoint B)]
    calc
      ∑ v∈B,(v.fiberOver (field K p)).card=∑ _v∈B,8 := Finset.sum_congr rfl hcard
      _=40 := by simp [B,support_card K p hp ha hb]
  have hsupp : Function.support (fun w : Place K (field K p) =>
      (w.ramificationIndex (RatFunc K) : ℤ)-1) ⊆ S := by
    intro w hw
    apply (hmem w).mpr
    by_contra hn
    have he : w.ramificationIndex (RatFunc K)=1 := by rw [actual_index_formula K p hp ha hb,if_neg hn]
    exact hw (by simp [he])
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  calc
    ∑ w∈S,((w.ramificationIndex (RatFunc K) : ℤ)-1)=∑ _w∈S,(1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [actual_index_formula K p hp ha hb,if_pos ((hmem w).mp hw)]
      norm_num
    _=40 := by simp [hScard]

/-- Genuine geometric genus five for the exact four-root Hasse function
field. The degree, every ramification index and the branch count are proved. -/
theorem genus_five (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    genusFF K (field K p)=5 := by
  letI : PerfectField K := IsAlgClosed.perfectField K
  letI := finite_over_line K p
  letI := separable K p
  letI : IsCurveOver K (RatFunc K) := RatFuncFiniteExtension.isCurveOver_of_perfectField K (RatFunc K)
  letI : IsCurveOver K (field K p) := isCurveOver K p
  have htame : ∀w : Place K (field K p),((w.ramificationIndex (RatFunc K) : ℕ) : K) ≠ 0 := by
    intro w
    rw [actual_index_formula K p hp ha hb w]
    split_ifs
    · exact NeZero.ne (2 : K)
    · simpa only [Nat.cast_one] using (one_ne_zero : (1 : K) ≠ 0)
  have hrh := two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
    (RatFuncFiniteExtension.base_oneVariable K) htame
  rw [field_degree_sixteen K p hp ha hb,RatFuncFiniteExtension.genus_base_eq_zero K,
    actual_ramification_sum K p hp ha hb] at hrh
  omega

theorem rational_geometric_genus_five (p : ℚ) (hp : 1<p) :
    genusFF (AlgebraicClosure ℚ) (field (AlgebraicClosure ℚ) (p : AlgebraicClosure ℚ))=5 := by
  apply genus_five
  · exact_mod_cast (show p ≠ 0 by linarith)
  · exact_mod_cast (show p-1 ≠ 0 by linarith)
  · exact_mod_cast (show p+1 ≠ 0 by linarith)

#print axioms actual_index_formula
#print axioms actual_ramification_sum
#print axioms genus_five
#print axioms rational_geometric_genus_five

end
end FourCorner.HpGeometricGenus
