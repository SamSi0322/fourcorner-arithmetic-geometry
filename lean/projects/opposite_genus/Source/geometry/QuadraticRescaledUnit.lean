import geometry.QuadraticUnitRamification
import Mathlib.Tactic

/-!
# Unramified square-root extensions after rescaling

Dividing a primitive square root by a nonzero base-field element preserves
generation. If the radicand has twice the order of that element, the rescaled
radicand is a unit at the actual restricted place, so the extension is unramified.
-/

noncomputable section

namespace FourCorner.QuadraticRescaledUnit

open AlgebraicCurve

/-- Dividing a generator by a nonzero base scalar preserves algebra generation. -/
theorem adjoin_div_algebraMap_eq_top {F E : Type*} [Field F] [Field E] [Algebra F E]
    (r : E) {t : F} (ht : t ≠ 0) (hgen : Algebra.adjoin F {r} = ⊤) :
    Algebra.adjoin F {r / algebraMap F E t} = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Algebra.adjoin_singleton_le
  have htE : algebraMap F E t ≠ 0 := (map_ne_zero (algebraMap F E)).mpr ht
  simpa only [div_mul_cancel₀ _ htE] using
    (Algebra.adjoin F {r / algebraMap F E t}).mul_mem
      (Algebra.subset_adjoin (Set.mem_singleton _))
      ((Algebra.adjoin F {r / algebraMap F E t}).algebraMap_mem t)

/-- The order of a quotient of nonzero functions at an actual place. -/
theorem ord_div {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    v.ord (a / b) = v.ord a - v.ord b := by
  rw [div_eq_mul_inv, v.ord_mul ha (inv_ne_zero hb), v.ord_inv, sub_eq_add_neg]

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [CharZero K]

/-- A square-root extension is unramified when a base element removes the entire
order of its radicand. The new generator and its zero-order radicand are derived. -/
theorem ramificationIndex_eq_one_of_ord_eq_twice
    (w : Place K E) {a t : F} {r : E}
    (hroot : r ^ 2 = algebraMap F E a)
    (hgen : Algebra.adjoin F {r} = ⊤)
    (ha : a ≠ 0) (ht : t ≠ 0)
    (hord : (w.restrict F).ord a = 2 * (w.restrict F).ord t) :
    w.ramificationIndex F = 1 := by
  have hroot' : (r / algebraMap F E t) ^ 2 = algebraMap F E (a / t ^ 2) := by
    rw [div_pow, hroot, map_div₀, map_pow]
  have hgen' := adjoin_div_algebraMap_eq_top r ht hgen
  have ha' : a / t ^ 2 ≠ 0 := div_ne_zero ha (pow_ne_zero _ ht)
  have htord : (w.restrict F).ord (t ^ 2) = 2 * (w.restrict F).ord t := by
    simpa only [zpow_ofNat] using (w.restrict F).ord_zpow t (2 : ℤ)
  have hord' : (w.restrict F).ord (a / t ^ 2) = 0 := by
    rw [ord_div (w.restrict F) ha (pow_ne_zero _ ht), htord, hord, sub_self]
  exact QuadraticUnitRamification.ramificationIndex_eq_one_of_unit_radicand
    w hroot' hgen' ha' hord'

end FourCorner.QuadraticRescaledUnit

#print axioms FourCorner.QuadraticRescaledUnit.adjoin_div_algebraMap_eq_top
#print axioms FourCorner.QuadraticRescaledUnit.ord_div
#print axioms FourCorner.QuadraticRescaledUnit.ramificationIndex_eq_one_of_ord_eq_twice
