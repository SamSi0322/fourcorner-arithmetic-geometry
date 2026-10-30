import geometry.QuadraticUnitRamification

noncomputable section
namespace FourCorner.OddQuadraticUnit
open AlgebraicCurve
attribute [local instance] FractionRing.liftAlgebra
variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

theorem index_one_of_different_top (w : Place K E)
    (hdiff : differentIdeal (w.restrict F).toValuationSubring
      (Place.integralClosureAt E (w.restrict F)) = ⊤) :
    w.ramificationIndex F = 1 := by
  let v := w.restrict F
  let A := v.toValuationSubring
  let B := Place.integralClosureAt E v
  let P := (Place.fiberCenter E v rfl).asIdeal
  haveI : Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A F).symm.toRingEquiv
      (FractionRing.algEquiv B E).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A F).symm
      (FractionRing.algEquiv B E).symm x
  have hP : P.IsPrime := (Place.fiberCenter E v rfl).isPrime
  have : P.LiesOver (IsLocalRing.maximalIdeal A) := Place.fiberCenter_liesOver rfl
  have : Algebra.IsUnramifiedAt A P := not_dvd_differentIdeal_iff.mp (by
    rw [hdiff]
    intro h
    exact hP.ne_top (top_unique (Ideal.le_of_dvd h)))
  rw [QuadraticUnitRamification.ramificationIndex_eq_ideal_index (w := w) (v := v) rfl,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Place.maximalIdeal_ne_bot v)]
  exact Ideal.ramificationIdx_eq_one P A

/-- A genuine primitive unit square root has unit different and e=1 over
any constants of characteristic different from two, including finite fields. -/
theorem unit_radicand [NeZero (2 : K)] (w : Place K E) {a : F} {r : E}
    (hroot : r ^ 2 = algebraMap F E a) (hgen : Algebra.adjoin F {r} = ⊤)
    (ha : a ≠ 0) (hord : (w.restrict F).ord a = 0) :
    differentIdeal (w.restrict F).toValuationSubring
      (Place.integralClosureAt E (w.restrict F)) = ⊤ ∧ w.ramificationIndex F = 1 := by
  let v := w.restrict F
  let A := v.toValuationSubring
  let B := Place.integralClosureAt E v
  have hav : v.adicValuation a = 1 := (v.ord_eq_zero_iff_adicValuation_eq_one ha).mp hord
  have ham : a ∈ A := v.mem_iff_adicValuation_le_one.mpr (le_of_eq hav)
  let u : A := ⟨a,ham⟩
  have hu : IsUnit u := (v.adicValuation_coe_eq_one_iff u).mp hav
  have hrI : IsIntegral A r := by
    apply IsIntegral.of_pow (show 0 < (2:ℕ) by decide)
    rw [hroot]
    exact isIntegral_algebraMap (x := u)
  let x : B := ⟨r,hrI⟩
  have hxroot : x^2 = algebraMap A B u := by apply Subtype.ext; exact hroot
  have hxgen : Algebra.adjoin F {algebraMap B E x} = ⊤ := hgen
  have htwo : IsUnit (2 : A) := by
    have hk : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr (NeZero.ne (2:K))
    simpa only [map_ofNat] using hk.map (algebraMap K A)
  have hd := QuadraticDifferentUnit.differentIdeal_eq_top_of_unit_root x u hxgen hxroot hu htwo
  exact ⟨hd,index_one_of_different_top w hd⟩
end FourCorner.OddQuadraticUnit
#print axioms FourCorner.OddQuadraticUnit.index_one_of_different_top
#print axioms FourCorner.OddQuadraticUnit.unit_radicand
