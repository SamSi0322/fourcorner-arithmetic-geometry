import CriticalBranchPlaces
import RadicalSeparable

noncomputable section
namespace FourCorner.CriticalActualRamification
open AlgebraicCurve AlgebraicCurve.RationalFunctionField
open CriticalRadicalField CriticalBranchPlaces
variable {K : Type*} [Field K]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
local instance : DecidableEq (RatFunc K):=Classical.decEq _
attribute [local instance] Classical.propDecidable

theorem roots_generate (i : K) : Algebra.adjoin (RatFunc K) {b K i,c K i}=⊤ :=
  Biquadratic.roots_generate_algebra (RatFunc K) _ _

theorem separable (i : K) (h2 : (2:K)≠0) : Algebra.IsSeparable (RatFunc K) (field K i) := by
  have h2F : (2:RatFunc K)≠0 := by
    simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap K (RatFunc K))).mpr h2
  let r : Fin 2 → field K i:=![b K i,c K i]
  apply RadicalSeparable.generated r
  · apply top_le_iff.mp
    rw [←roots_generate (K:=K) i]
    apply Algebra.adjoin_mono
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl|rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  · intro a
    fin_cases a
    · exact RadicalSeparable.square_root (Biquadratic.root₁_sq (RatFunc K) _ _) h2F
    · exact RadicalSeparable.square_root (Biquadratic.root₂_sq (RatFunc K) _ _) h2F

/-- Parity formula on the SAME literal radical field, including every place. -/
theorem parity_index (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) (w : Place K (field K i)) :
    w.ramificationIndex (RatFunc K)=if Even ((w.restrict (RatFunc K)).ord (radicand i 0)) ∧
      Even ((w.restrict (RatFunc K)).ord (radicand i 1)) then 1 else 2 := by
  letI : NeZero (2:K):=⟨h2⟩
  exact CriticalTwoRamification.index_formula w (radicand i 0) (radicand i 1) (b K i) (c K i)
    (Biquadratic.root₁_sq (RatFunc K) _ _) (Biquadratic.root₂_sq (RatFunc K) _ _)
    (radicand_ne_zero i hi h2 0) (radicand_ne_zero i hi h2 1) (roots_generate i)

/-- Exact index-two support on four ACTUAL finite base places, and e=1 at
all other actual places, including infinity. No ramification premise. -/
theorem index_formula [IsAlgClosed K] (i : K) (hi : i^2= -1) (h2 : (2:K)≠0)
    (w : Place K (field K i)) :
    w.ramificationIndex (RatFunc K)=if w.restrict (RatFunc K)∈branch i then 2 else 1 := by
  classical
  rw [parity_index i hi h2]
  rcases eq_placeOfPoint_or_eq_placeInfty K (w.restrict (RatFunc K)) with ⟨z,hz⟩|hz
  · rw [hz,ord_finite i hi h2 0,ord_finite i hi h2 1]
    simp only [finite_mem_branch i hi h2]
    by_cases hb : (polynomial i 0).eval z=0 <;> by_cases hc : (polynomial i 1).eval z=0 <;> simp [hb,hc]
  · rw [hz,ord_infty i hi h2 0,ord_infty i hi h2 1,if_neg (infty_not_branch i)]
    norm_num

theorem tame [IsAlgClosed K] (i : K) (hi : i^2= -1) (h2 : (2:K)≠0)
    (w : Place K (field K i)) : ((w.ramificationIndex (RatFunc K):ℕ):K)≠0 := by
  rw [index_formula i hi h2]
  split_ifs
  · exact h2
  · simpa only [Nat.cast_one] using (one_ne_zero : (1:K)≠0)
end FourCorner.CriticalActualRamification
#print axioms FourCorner.CriticalActualRamification.separable
#print axioms FourCorner.CriticalActualRamification.parity_index
#print axioms FourCorner.CriticalActualRamification.index_formula
#print axioms FourCorner.CriticalActualRamification.tame
