import CriticalActualRamification
import geometry.QuadraticPlaceRamification

noncomputable section
namespace FourCorner.CriticalFiberBounds
open AlgebraicCurve
variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- No residue-degree-one premise: actual positive inertia degrees and the
native e*f fundamental identity bound every actual fiber. -/
theorem mul_card_le_finrank (v : Place K F) (d : ℕ)
    (he : ∀ w∈v.fiberOver E,d≤w.ramificationIndex F) :
    d*(v.fiberOver E).card≤Module.finrank F E := by
  classical
  have hs : (∑ w∈v.fiberOver E,(d:ℤ))≤
      ∑ w∈v.fiberOver E,(w.ramificationIndex F:ℤ)*(w.inertiaDeg F:ℤ) := by
    apply Finset.sum_le_sum
    intro w hw
    have hew : (d:ℤ)≤w.ramificationIndex F := by exact_mod_cast he w hw
    have hfw : (1:ℤ)≤w.inertiaDeg F := by exact_mod_cast QuadraticPlaceRamification.inertiaDeg_pos w
    have hpos : (0:ℤ)≤w.ramificationIndex F:=Int.natCast_nonneg _
    nlinarith
  rw [v.sum_ramificationIndex_mul_inertiaDeg_fiberOver] at hs
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  exact_mod_cast (show (d:ℤ)*(v.fiberOver E).card≤Module.finrank F E by simpa only [mul_comm] using hs)

theorem card_le_finrank (v : Place K F) : (v.fiberOver E).card≤Module.finrank F E := by
  have h:=mul_card_le_finrank (E:=E) v 1 (fun w _=>w.ramificationIndex_pos (F:=F))
  simpa only [one_mul] using h

theorem card_le_two (hdegree : Module.finrank F E=4) (v : Place K F)
    (he : ∀ w∈v.fiberOver E,2≤w.ramificationIndex F) : (v.fiberOver E).card≤2 := by
  have h:=mul_card_le_finrank v 2 he
  rw [hdegree] at h
  omega
end FourCorner.CriticalFiberBounds
#print axioms FourCorner.CriticalFiberBounds.card_le_finrank
#print axioms FourCorner.CriticalFiberBounds.card_le_two
