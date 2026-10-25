import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import geometry.QuadraticDifferentUnit
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Tactic

noncomputable section

/-!
# Unit radicands are unramified at genuine places

The integral closure of the actual place valuation ring is used to calculate the
different. Its triviality is transported through the accepted place/ideal-index
dictionary. No ramification index or unramifiedness assumption is supplied.
-/

namespace FourCorner.QuadraticUnitRamification

open AlgebraicCurve

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem ramificationIndex_eq_ideal_index {v : Place K F} {w : Place K E}
    (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (Place.fiberCenter E v hw).asIdeal := by
  exact P2MW.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg.AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter hw

theorem ramificationIndex_eq_one_of_differentIdeal_eq_top [CharZero K]
    (w : Place K E)
    (hdiff : differentIdeal (w.restrict F).toValuationSubring
      (Place.integralClosureAt E (w.restrict F)) = ⊤) :
    w.ramificationIndex F = 1 := by
  let v := w.restrict F
  let A := v.toValuationSubring
  let B := Place.integralClosureAt E v
  let P := (Place.fiberCenter E v rfl).asIdeal
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hP : P.IsPrime := (Place.fiberCenter E v rfl).isPrime
  have : P.LiesOver (IsLocalRing.maximalIdeal A) := Place.fiberCenter_liesOver rfl
  have : Algebra.IsUnramifiedAt A P := not_dvd_differentIdeal_iff.mp (by
    rw [hdiff]
    intro h
    exact hP.ne_top (top_unique (Ideal.le_of_dvd h)))
  rw [ramificationIndex_eq_ideal_index (w := w) (v := v) rfl,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Place.maximalIdeal_ne_bot v)]
  exact Ideal.ramificationIdx_eq_one P A

/-- A square-root generator with nonzero radicand of order zero is unramified.
No extension-degree assumption is needed; a trivial adjunction is included. -/
theorem ramificationIndex_eq_one_of_unit_radicand [CharZero K]
    (w : Place K E) {a : F} {r : E}
    (hroot : r ^ 2 = algebraMap F E a)
    (hgen : Algebra.adjoin F {r} = ⊤)
    (ha : a ≠ 0) (hord : (w.restrict F).ord a = 0) :
    w.ramificationIndex F = 1 := by
  let v := w.restrict F
  let A := v.toValuationSubring
  let B := Place.integralClosureAt E v
  have hav : v.adicValuation a = 1 :=
    (v.ord_eq_zero_iff_adicValuation_eq_one ha).mp hord
  have ham : a ∈ A := v.mem_iff_adicValuation_le_one.mpr (le_of_eq hav)
  let u : A := ⟨a, ham⟩
  have hu : IsUnit u := (v.adicValuation_coe_eq_one_iff u).mp hav
  have hrI : IsIntegral A r := by
    apply IsIntegral.of_pow (show 0 < (2 : ℕ) by decide)
    rw [hroot]
    exact isIntegral_algebraMap (x := u)
  let x : B := ⟨r, hrI⟩
  have hxroot : x ^ 2 = algebraMap A B u := by
    apply Subtype.ext
    exact hroot
  have hxgen : Algebra.adjoin F {algebraMap B E x} = ⊤ := hgen
  have htwo : IsUnit (2 : A) := by
    have htwoK : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr (by norm_num)
    simpa only [map_ofNat] using htwoK.map (algebraMap K A)
  apply ramificationIndex_eq_one_of_differentIdeal_eq_top w
  exact QuadraticDifferentUnit.differentIdeal_eq_top_of_unit_root x u hxgen hxroot hu htwo

end FourCorner.QuadraticUnitRamification

#print axioms FourCorner.QuadraticUnitRamification.ramificationIndex_eq_one_of_differentIdeal_eq_top
#print axioms FourCorner.QuadraticUnitRamification.ramificationIndex_eq_one_of_unit_radicand
