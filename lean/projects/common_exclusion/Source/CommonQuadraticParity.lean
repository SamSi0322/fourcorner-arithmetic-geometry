import geometry.QuadraticPlaceRamification
import CommonGenus17Unramified
import CommonTower

noncomputable section
namespace FourCorner.CommonQuadraticParity
open AlgebraicCurve
variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [CharZero K]

theorem index_formula (w : Place K E) {a : F} {r : E}
    (hr : r^2 = algebraMap F E a) (hgen : Algebra.adjoin F {r} = ⊤)
    (ha : a ≠ 0) (hdegree : Module.finrank F E ≤ 2) :
    w.ramificationIndex F = if Even ((w.restrict F).ord a) then 1 else 2 := by
  classical
  split_ifs with he
  · exact CommonGenus17Unramified.unramified_of_even_order w hr hgen ha he
  · exact QuadraticPlaceRamification.ramificationIndex_eq_two_of_odd_ord w hr
      (Int.not_even_iff_odd.mp he) hdegree

lemma parity_accumulate (p : Prop) [Decidable p] (n : ℤ) :
    (if p then (1:ℕ) else 2) *
      (if Even ((if p then (1:ℤ) else 2)*n) then (1:ℕ) else 2) =
      if p ∧ Even n then 1 else 2 := by
  classical
  by_cases hp : p
  · simp [hp]
  · have he : Even ((2:ℤ)*n) := even_two.mul_right n
    simp [hp,he]

#print axioms index_formula
end FourCorner.CommonQuadraticParity
