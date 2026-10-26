import CriticalRamificationSum

noncomputable section
namespace FourCorner.CriticalGeometricGenus
open AlgebraicCurve AlgebraicCurve.RationalFunctionField
variable {K : Type*} [Field K] [IsAlgClosed K]
local instance : DecidableEq (RatFunc K):=Classical.decEq _

theorem infinity_unramified (i : K) (hi : i^2= -1) (h2 : (2:K)≠0)
    (w : Place K (CriticalRadicalField.field K i))
    (hw : w.restrict (RatFunc K)=placeInfty K) : w.ramificationIndex (RatFunc K)=1 := by
  rw [CriticalActualRamification.index_formula i hi h2,hw,
    if_neg (CriticalBranchPlaces.infty_not_branch i)]

/-- Genuine tame Riemann--Hurwitz on the ACTUAL literal two-root field.
The four genuine finite branch fibers have e2 and contribute8; every other
place, including all infinity places, has e1. Nothing is assigned as genus. -/
theorem genus_one (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) :
    genusFF K (CriticalRadicalField.field K i)=1 := by
  letI : PerfectField K:=IsAlgClosed.perfectField K
  letI := CriticalActualRamification.separable i h2
  letI : IsCurveOver K (RatFunc K):=RatFuncFiniteExtension.isCurveOver_of_perfectField K (RatFunc K)
  letI := CriticalRadicalField.isCurveOver K i
  have hrh:=two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
    (RatFuncFiniteExtension.base_oneVariable K) (CriticalActualRamification.tame i hi h2)
  rw [CriticalRadicalField.degree_four K i hi h2,RatFuncFiniteExtension.genus_base_eq_zero K,
    CriticalRamificationSum.actual_sum i hi h2] at hrh
  omega
end FourCorner.CriticalGeometricGenus
#print axioms FourCorner.CriticalGeometricGenus.infinity_unramified
#print axioms FourCorner.CriticalGeometricGenus.genus_one
