import CriticalActualRamification
import geometry.BiquadraticRamificationSum

noncomputable section
namespace FourCorner.CriticalRamificationSum
open AlgebraicCurve
attribute [local instance] Classical.propDecidable

section Generic
variable {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K E]

theorem sum_e_sub_one (B : Finset (Place K F)) (hB : B.card=4)
    (hdegree : Module.finrank F E=4)
    (he : ∀ w : Place K E,w.ramificationIndex F=if w.restrict F∈B then 2 else 1) :
    (∑ᶠ w : Place K E,((w.ramificationIndex F:ℤ)-1))=8 := by
  classical
  let S:=B.biUnion (fun v=>v.fiberOver E)
  have hmem (w : Place K E) : w∈S ↔ w.restrict F∈B := by
    simp only [S,Finset.mem_biUnion,Place.mem_fiberOver]
    constructor
    · rintro ⟨v,hv,hw⟩;exact hw.symm ▸ hv
    · intro hw;exact ⟨w.restrict F,hw,rfl⟩
  have hcard (v : Place K F) (hv : v∈B) : (v.fiberOver E).card=2 := by
    apply BiquadraticRamificationSum.card_fiberOver_eq_two hdegree v
    · intro w hw;rw [he w,v.restrict_eq_of_mem_fiberOver hw,if_pos hv]
    · intro w _;exact RamificationSum.inertiaDeg_eq_one w
  have hScard : S.card=8 := by
    dsimp [S]
    rw [Finset.card_biUnion (RamificationSum.fibers_pairwiseDisjoint B)]
    calc
      ∑ v∈B,(v.fiberOver E).card=∑ _v∈B,2:=Finset.sum_congr rfl hcard
      _=8:=by simp [hB]
  have hsupp : Function.support (fun w : Place K E=>(w.ramificationIndex F:ℤ)-1)⊆S := by
    intro w hw
    apply (hmem w).mpr
    by_contra hn
    have hh : w.ramificationIndex F=1 := by rw [he w,if_neg hn]
    exact hw (by simp [hh])
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  calc
    ∑ w∈S,((w.ramificationIndex F:ℤ)-1)=∑ _w∈S,(1:ℤ) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [he w,if_pos ((hmem w).mp hw)]
      norm_num
    _=8 := by simp [hScard]
end Generic

variable {K : Type*} [Field K] [IsAlgClosed K]
local instance : DecidableEq (Place K (RatFunc K)):=Classical.decEq _

theorem actual_sum (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) :
    (∑ᶠ w : Place K (CriticalRadicalField.field K i),
      ((w.ramificationIndex (RatFunc K):ℤ)-1))=8 := by
  letI : PerfectField K:=IsAlgClosed.perfectField K
  letI := CriticalActualRamification.separable i h2
  letI : IsCurveOver K (RatFunc K):=RatFuncFiniteExtension.isCurveOver_of_perfectField K (RatFunc K)
  letI := CriticalRadicalField.isCurveOver K i
  exact sum_e_sub_one (CriticalBranchPlaces.branch i) (CriticalBranchPlaces.branch_card i hi h2)
    (CriticalRadicalField.degree_four K i hi h2) (CriticalActualRamification.index_formula i hi h2)

/-- Every one of the four actual geometric branch fibers has exactly two
actual places, from the e*f fundamental identity and derived residue degree1. -/
theorem actual_branch_fiber (i : K) (hi : i^2= -1) (h2 : (2:K)≠0)
    (v : Place K (RatFunc K)) (hv : v∈CriticalBranchPlaces.branch i) :
    letI := CriticalActualRamification.separable i h2
    (v.fiberOver (CriticalRadicalField.field K i)).card=2 := by
  letI : PerfectField K:=IsAlgClosed.perfectField K
  letI := CriticalActualRamification.separable i h2
  letI : IsCurveOver K (RatFunc K):=RatFuncFiniteExtension.isCurveOver_of_perfectField K (RatFunc K)
  letI := CriticalRadicalField.isCurveOver K i
  apply BiquadraticRamificationSum.card_fiberOver_eq_two (CriticalRadicalField.degree_four K i hi h2) v
  · intro w hw
    rw [CriticalActualRamification.index_formula i hi h2,v.restrict_eq_of_mem_fiberOver hw,if_pos hv]
  · intro w _;exact RamificationSum.inertiaDeg_eq_one w
end FourCorner.CriticalRamificationSum
#print axioms FourCorner.CriticalRamificationSum.actual_sum
#print axioms FourCorner.CriticalRamificationSum.actual_branch_fiber
