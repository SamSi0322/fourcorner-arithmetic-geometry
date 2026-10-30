import CriticalRadicalField
import OddFourTower

noncomputable section
namespace FourCorner.CriticalTwoRamification
open AlgebraicCurve
variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [NeZero (2:K)]

/-- Two actual primitive radicals have index one exactly when both actual
base-place orders are even; the auxiliary unit roots do not change the field. -/
theorem index_formula (w : Place K E) (a b : F) (r s : E)
    (hr : r^2=algebraMap F E a) (hs : s^2=algebraMap F E b)
    (ha : a≠0) (hb : b≠0) (hgen : Algebra.adjoin F {r,s}=⊤) :
    w.ramificationIndex F=
      if Even ((w.restrict F).ord a) ∧ Even ((w.restrict F).ord b) then 1 else 2 := by
  classical
  have hg : Algebra.adjoin F {r,s,(1:E),1}=⊤ := by
    apply top_le_iff.mp
    rw [←hgen]
    apply Algebra.adjoin_mono
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢
    tauto
  have hh:=OddFourTower.index_formula w a b 1 1 r s 1 1 hr hs
    (by simp) (by simp) ha hb one_ne_zero one_ne_zero hg
  simpa using hh
end FourCorner.CriticalTwoRamification
#print axioms FourCorner.CriticalTwoRamification.index_formula
