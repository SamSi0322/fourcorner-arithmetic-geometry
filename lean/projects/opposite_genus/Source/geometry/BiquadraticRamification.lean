import geometry.BiquadraticField
import geometry.MultiquadraticRamification

/-!
# Actual ramification in a two-radical field

These statements compute the indices of actual places in the two quadratic
stages. The generators and degrees come from the constructed fields.
-/

noncomputable section

namespace FourCorner.Biquadratic.Ramification

open AlgebraicCurve Multiquadratic.Tower

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]

private theorem nonsquare_ne_zero {a : F} (ha : ¬ IsSquare a) : a ≠ 0 := by
  intro h
  apply ha
  simp [h]

private theorem first_unit (a b : F) (w : Place K (field F a b))
    (ha : a ≠ 0) (hord : (w.restrict F).ord a = 0) :
    (w.restrict (first F a)).ramificationIndex F = 1 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  apply QuadraticUnitRamification.ramificationIndex_eq_one_of_unit_radicand
    (w.restrict (first F a)) (stepRoot₁_sq F a) (stepRoot₁_generates F a) ha
  simpa only [PlaceTower.restrict_restrict] using hord

private theorem second_unit (a b : F) (w : Place K (field F a b))
    (hb : b ≠ 0) (hord : (w.restrict F).ord b = 0) :
    w.ramificationIndex (first F a) = 1 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  apply QuadraticUnitRamification.ramificationIndex_eq_one_of_unit_radicand w
    (stepRoot₂_sq F a b) (stepRoot₂_generates F a b)
    ((map_ne_zero (algebraMap F (first F a))).mpr hb)
  rw [(w.restrict (first F a)).ord_restrict b, PlaceTower.restrict_restrict, hord,
    mul_zero]

/-- A simple zero of the first radicand and a unit second radicand give index two. -/
theorem ramificationIndex_eq_two_10 (a b : F)
    (hind : IndependentSquareclasses F a b) (w : Place K (field F a b))
    (ha : (w.restrict F).ord a = 1) (hb : (w.restrict F).ord b = 0) :
    w.ramificationIndex F = 2 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have h₁ : (w.restrict (first F a)).ramificationIndex F = 2 := by
    apply QuadraticPlaceRamification.ramificationIndex_eq_two_of_ord_eq_one
      (w.restrict (first F a)) (stepRoot₁_sq F a) _
      (le_of_eq (finrank_first F a hind.first))
    simpa only [PlaceTower.restrict_restrict] using ha
  have h₂ := second_unit a b w (nonsquare_ne_zero hind.second) hb
  rw [PlaceTower.ramificationIndex_mul (E := first F a), h₁, h₂, one_mul]

/-- A unit first radicand and a simple zero of the second radicand give index two. -/
theorem ramificationIndex_eq_two_01 (a b : F)
    (hind : IndependentSquareclasses F a b) (w : Place K (field F a b))
    (ha : (w.restrict F).ord a = 0) (hb : (w.restrict F).ord b = 1) :
    w.ramificationIndex F = 2 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have h₁ := first_unit a b w (nonsquare_ne_zero hind.first) ha
  have h₂ : w.ramificationIndex (first F a) = 2 := by
    apply QuadraticPlaceRamification.ramificationIndex_eq_two_of_ord_eq_one w
      (stepRoot₂_sq F a b) _ (le_of_eq (finrank_step₂ F a b (by norm_num) hind))
    rw [(w.restrict (first F a)).ord_restrict b, PlaceTower.restrict_restrict, h₁, hb]
    norm_num
  rw [PlaceTower.ramificationIndex_mul (E := first F a), h₁, h₂, mul_one]

/-- A common base function removing both radicand orders makes the actual extension unramified. -/
theorem ramificationIndex_eq_one_of_common_twice (a b : F)
    (hind : IndependentSquareclasses F a b) (w : Place K (field F a b))
    {t : F} (ht : t ≠ 0)
    (ha : (w.restrict F).ord a = 2 * (w.restrict F).ord t)
    (hb : (w.restrict F).ord b = 2 * (w.restrict F).ord t) :
    w.ramificationIndex F = 1 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have h₁ : (w.restrict (first F a)).ramificationIndex F = 1 := by
    apply QuadraticRescaledUnit.ramificationIndex_eq_one_of_ord_eq_twice
      (w.restrict (first F a)) (stepRoot₁_sq F a) (stepRoot₁_generates F a)
      (nonsquare_ne_zero hind.first) ht
    simpa only [PlaceTower.restrict_restrict] using ha
  have hb₁ : (w.restrict (first F a)).ord (algebraMap F (first F a) b) =
      2 * (w.restrict (first F a)).ord (algebraMap F (first F a) t) := by
    rw [(w.restrict (first F a)).ord_restrict b,
      (w.restrict (first F a)).ord_restrict t]
    simp only [PlaceTower.restrict_restrict]
    rw [hb]
    ring
  have h₂ : w.ramificationIndex (first F a) = 1 :=
    QuadraticRescaledUnit.ramificationIndex_eq_one_of_ord_eq_twice w
      (stepRoot₂_sq F a b) (stepRoot₂_generates F a b)
      ((map_ne_zero (algebraMap F (first F a))).mpr (nonsquare_ne_zero hind.second))
      ((map_ne_zero (algebraMap F (first F a))).mpr ht) hb₁
  rw [PlaceTower.ramificationIndex_mul (E := first F a), h₁, h₂, mul_one]

/-- The all-unit pattern is unramified. -/
theorem ramificationIndex_eq_one_of_orders_zero (a b : F)
    (hind : IndependentSquareclasses F a b) (w : Place K (field F a b))
    (ha : (w.restrict F).ord a = 0) (hb : (w.restrict F).ord b = 0) :
    w.ramificationIndex F = 1 := by
  apply ramificationIndex_eq_one_of_common_twice a b hind w (t := 1) one_ne_zero
  · simpa using ha
  · simpa using hb

end FourCorner.Biquadratic.Ramification

#print axioms FourCorner.Biquadratic.Ramification.ramificationIndex_eq_two_10
#print axioms FourCorner.Biquadratic.Ramification.ramificationIndex_eq_two_01
#print axioms FourCorner.Biquadratic.Ramification.ramificationIndex_eq_one_of_common_twice
#print axioms FourCorner.Biquadratic.Ramification.ramificationIndex_eq_one_of_orders_zero
