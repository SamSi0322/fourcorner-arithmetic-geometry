import ThetaCoverClassPortable.geometry.MultiquadraticTower
import ThetaCoverClassPortable.geometry.PlaceTower
import ThetaCoverClassPortable.geometry.QuadraticPlaceRamification
import ThetaCoverClassPortable.geometry.QuadraticUnitRamification
import ThetaCoverClassPortable.geometry.QuadraticRescaledUnit

/-!
# Actual ramification in the three-radical field

The stage fields, square-root generators, dimensions, and generation proofs
come from `MultiquadraticTower`. Every ramification index below is the actual
index of a place; the total index is computed by the field-tower formula.
-/

noncomputable section

namespace FourCorner.Multiquadratic.Tower

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

instance (priority := 900) constantAlgebraFirst (a : F) : Algebra K (first F a) :=
  ((algebraMap F (first F a)).comp (algebraMap K F)).toAlgebra

instance (priority := 900) constantAlgebraSecond (a b : F) : Algebra K (second F a b) :=
  ((algebraMap F (second F a b)).comp (algebraMap K F)).toAlgebra

instance (priority := 900) constantAlgebraThird (a b c : F) : Algebra K (third F a b c) :=
  ((algebraMap F (third F a b c)).comp (algebraMap K F)).toAlgebra

instance constantTowerFirst (a : F) : IsScalarTower K F (first F a) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance constantTowerSecond (a b : F) : IsScalarTower K F (second F a b) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance constantTowerThird (a b c : F) : IsScalarTower K F (third F a b c) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance constantTower₁₂ (a b : F) : IsScalarTower K (first F a) (second F a b) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance constantTower₂₃ (a b c : F) : IsScalarTower K (second F a b) (third F a b c) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance constantTower₁₃ (a b c : F) : IsScalarTower K (first F a) (third F a b c) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end FourCorner.Multiquadratic.Tower

set_option linter.unusedSectionVars false
namespace FourCorner.ThreeQuadraticPatterns
open AlgebraicCurve
variable {K F A B E : Type*} [Field K] [Field F] [Field A] [Field B] [Field E]
  [CharZero K]
  [Algebra K F] [Algebra K A] [Algebra K B] [Algebra K E]
  [Algebra F A] [Algebra F B] [Algebra F E]
  [Algebra A B] [Algebra A E] [Algebra B E]
  [IsScalarTower K F A] [IsScalarTower K F B] [IsScalarTower K F E]
  [IsScalarTower K A B] [IsScalarTower K A E] [IsScalarTower K B E]
  [IsScalarTower F A B] [IsScalarTower F A E] [IsScalarTower F B E]
  [IsScalarTower A B E]
  [FiniteDimensional F A] [FiniteDimensional F B] [FiniteDimensional F E]
  [FiniteDimensional A B] [FiniteDimensional A E] [FiniteDimensional B E]
  [Algebra.IsSeparable F A] [Algebra.IsSeparable A B] [Algebra.IsSeparable B E]

variable (w : Place K E)

lemma ord_restrict_first (a : F) :
    ((w.restrict B).restrict A).ord (algebraMap F A a) =
      ((w.restrict A).ramificationIndex F : ℤ) * (w.restrict F).ord a := by
  rw [PlaceTower.restrict_restrict, Place.ord_restrict,
    PlaceTower.restrict_restrict]

lemma ord_restrict_second (a : F) :
    (w.restrict B).ord (algebraMap A B (algebraMap F A a)) =
      ((w.restrict B).ramificationIndex F : ℤ) * (w.restrict F).ord a := by
  rw [← IsScalarTower.algebraMap_apply F A B, Place.ord_restrict,
    PlaceTower.restrict_restrict]

lemma first_unit {a : F} {r : A}
    (hroot : r ^ 2 = algebraMap F A a)
    (hgen : Algebra.adjoin F {r} = ⊤) (ha : a ≠ 0)
    (hord : (w.restrict F).ord a = 0) :
    (w.restrict A).ramificationIndex F = 1 := by
  apply QuadraticUnitRamification.ramificationIndex_eq_one_of_unit_radicand
    (w.restrict A) hroot hgen ha
  rwa [PlaceTower.restrict_restrict]

lemma second_unit {b : F} {r : B}
    (hroot : r ^ 2 = algebraMap A B (algebraMap F A b))
    (hgen : Algebra.adjoin A {r} = ⊤) (hb : b ≠ 0)
    (hord : (w.restrict F).ord b = 0) :
    (w.restrict B).ramificationIndex A = 1 := by
  apply QuadraticUnitRamification.ramificationIndex_eq_one_of_unit_radicand
    (w.restrict B) hroot hgen ((map_ne_zero (algebraMap F A)).2 hb)
  rw [ord_restrict_first, hord, mul_zero]

lemma third_unit {c : F} {r : E}
    (hroot : r ^ 2 = algebraMap B E (algebraMap A B (algebraMap F A c)))
    (hgen : Algebra.adjoin B {r} = ⊤) (hc : c ≠ 0)
    (hord : (w.restrict F).ord c = 0) : w.ramificationIndex B = 1 := by
  apply QuadraticUnitRamification.ramificationIndex_eq_one_of_unit_radicand
    w hroot hgen ((map_ne_zero (algebraMap A B)).2 ((map_ne_zero (algebraMap F A)).2 hc))
  rw [ord_restrict_second, hord, mul_zero]

lemma first_simple_zero {a : F} {r : A}
    (hroot : r ^ 2 = algebraMap F A a)
    (hord : (w.restrict F).ord a = 1)
    (hdegree : Module.finrank F A ≤ 2) :
    (w.restrict A).ramificationIndex F = 2 := by
  apply QuadraticPlaceRamification.ramificationIndex_eq_two_of_ord_eq_one
    (w.restrict A) hroot _ hdegree
  rwa [PlaceTower.restrict_restrict]

lemma second_simple_zero {b : F} {r : B}
    (hroot : r ^ 2 = algebraMap A B (algebraMap F A b))
    (hord : (w.restrict F).ord b = 1)
    (hfirst : (w.restrict A).ramificationIndex F = 1)
    (hdegree : Module.finrank A B ≤ 2) :
    (w.restrict B).ramificationIndex A = 2 := by
  apply QuadraticPlaceRamification.ramificationIndex_eq_two_of_ord_eq_one
    (w.restrict B) hroot _ hdegree
  rw [ord_restrict_first, hfirst, hord]
  norm_num

lemma third_simple_zero {c : F} {r : E}
    (hroot : r ^ 2 = algebraMap B E (algebraMap A B (algebraMap F A c)))
    (hord : (w.restrict F).ord c = 1)
    (hfirst : (w.restrict A).ramificationIndex F = 1)
    (hsecond : (w.restrict B).ramificationIndex A = 1)
    (hdegree : Module.finrank B E ≤ 2) : w.ramificationIndex B = 2 := by
  apply QuadraticPlaceRamification.ramificationIndex_eq_two_of_ord_eq_one w hroot _ hdegree
  rw [ord_restrict_second, PlaceTower.ramificationIndex_mul (E := A),
    PlaceTower.restrict_restrict, hfirst, hsecond, hord]
  norm_num

variable {a b c : F} {r₁ : A} {r₂ : B} {r₃ : E}

 theorem ramificationIndex_eq_one_000
    (hroot₁ : r₁ ^ 2 = algebraMap F A a)
    (hroot₂ : r₂ ^ 2 = algebraMap A B (algebraMap F A b))
    (hroot₃ : r₃ ^ 2 = algebraMap B E (algebraMap A B (algebraMap F A c)))
    (hgen₁ : Algebra.adjoin F {r₁} = ⊤)
    (hgen₂ : Algebra.adjoin A {r₂} = ⊤)
    (hgen₃ : Algebra.adjoin B {r₃} = ⊤)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hoa : (w.restrict F).ord a = 0)
    (hob : (w.restrict F).ord b = 0)
    (hoc : (w.restrict F).ord c = 0) : w.ramificationIndex F = 1 := by
  rw [PlaceTower.ramificationIndex_mul_three (E := A) (L := B),
    first_unit w hroot₁ hgen₁ ha hoa, second_unit w hroot₂ hgen₂ hb hob,
    third_unit w hroot₃ hgen₃ hc hoc]

 theorem ramificationIndex_eq_two_100
    (hroot₁ : r₁ ^ 2 = algebraMap F A a)
    (hroot₂ : r₂ ^ 2 = algebraMap A B (algebraMap F A b))
    (hroot₃ : r₃ ^ 2 = algebraMap B E (algebraMap A B (algebraMap F A c)))
    (hgen₂ : Algebra.adjoin A {r₂} = ⊤)
    (hgen₃ : Algebra.adjoin B {r₃} = ⊤)
    (hdegree₁ : Module.finrank F A ≤ 2)
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hoa : (w.restrict F).ord a = 1)
    (hob : (w.restrict F).ord b = 0)
    (hoc : (w.restrict F).ord c = 0) : w.ramificationIndex F = 2 := by
  rw [PlaceTower.ramificationIndex_mul_three (E := A) (L := B),
    first_simple_zero w hroot₁ hoa hdegree₁, second_unit w hroot₂ hgen₂ hb hob,
    third_unit w hroot₃ hgen₃ hc hoc]

 theorem ramificationIndex_eq_two_010
    (hroot₁ : r₁ ^ 2 = algebraMap F A a)
    (hroot₂ : r₂ ^ 2 = algebraMap A B (algebraMap F A b))
    (hroot₃ : r₃ ^ 2 = algebraMap B E (algebraMap A B (algebraMap F A c)))
    (hgen₁ : Algebra.adjoin F {r₁} = ⊤)
    (hgen₃ : Algebra.adjoin B {r₃} = ⊤)
    (hdegree₂ : Module.finrank A B ≤ 2)
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hoa : (w.restrict F).ord a = 0)
    (hob : (w.restrict F).ord b = 1)
    (hoc : (w.restrict F).ord c = 0) : w.ramificationIndex F = 2 := by
  have hfirst := first_unit w hroot₁ hgen₁ ha hoa
  rw [PlaceTower.ramificationIndex_mul_three (E := A) (L := B), hfirst,
    second_simple_zero w hroot₂ hob hfirst hdegree₂,
    third_unit w hroot₃ hgen₃ hc hoc]

 theorem ramificationIndex_eq_two_001
    (hroot₁ : r₁ ^ 2 = algebraMap F A a)
    (hroot₂ : r₂ ^ 2 = algebraMap A B (algebraMap F A b))
    (hroot₃ : r₃ ^ 2 = algebraMap B E (algebraMap A B (algebraMap F A c)))
    (hgen₁ : Algebra.adjoin F {r₁} = ⊤)
    (hgen₂ : Algebra.adjoin A {r₂} = ⊤)
    (hdegree₃ : Module.finrank B E ≤ 2)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hoa : (w.restrict F).ord a = 0)
    (hob : (w.restrict F).ord b = 0)
    (hoc : (w.restrict F).ord c = 1) : w.ramificationIndex F = 2 := by
  have hfirst := first_unit w hroot₁ hgen₁ ha hoa
  have hsecond := second_unit w hroot₂ hgen₂ hb hob
  rw [PlaceTower.ramificationIndex_mul_three (E := A) (L := B), hfirst, hsecond,
    third_simple_zero w hroot₃ hoc hfirst hsecond hdegree₃]

end FourCorner.ThreeQuadraticPatterns

namespace FourCorner.Multiquadratic.Ramification

open AlgebraicCurve Tower

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]

private theorem nonsquare_ne_zero {a : F} (ha : ¬ IsSquare a) : a ≠ 0 := by
  intro h
  apply ha
  simp [h]

private theorem stepRoot₃_sq_iterated (a b c : F) :
    stepRoot₃ F a b c ^ 2 = algebraMap (second F a b) (third F a b c)
      (algebraMap (first F a) (second F a b) (algebraMap F (first F a) c)) := by
  rw [← IsScalarTower.algebraMap_apply F (first F a) (second F a b)]
  exact stepRoot₃_sq F a b c

/-- The first radicand has a simple zero and the other two are units. -/
theorem ramificationIndex_eq_two_100 (a b c : F)
    (hind : IndependentSquareclasses F a b c) (w : Place K (third F a b c))
    (ha : (w.restrict F).ord a = 1) (hb : (w.restrict F).ord b = 0)
    (hc : (w.restrict F).ord c = 0) : w.ramificationIndex F = 2 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  exact ThreeQuadraticPatterns.ramificationIndex_eq_two_100 w
    (stepRoot₁_sq F a) (stepRoot₂_sq F a b) (stepRoot₃_sq_iterated a b c)
    (stepRoot₂_generates F a b) (stepRoot₃_generates F a b c)
    (le_of_eq (finrank_first F a hind.first))
    (nonsquare_ne_zero hind.second) (nonsquare_ne_zero hind.third) ha hb hc

/-- The second radicand has a simple zero and the other two are units. -/
theorem ramificationIndex_eq_two_010 (a b c : F)
    (hind : IndependentSquareclasses F a b c) (w : Place K (third F a b c))
    (ha : (w.restrict F).ord a = 0) (hb : (w.restrict F).ord b = 1)
    (hc : (w.restrict F).ord c = 0) : w.ramificationIndex F = 2 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  exact ThreeQuadraticPatterns.ramificationIndex_eq_two_010 w
    (stepRoot₁_sq F a) (stepRoot₂_sq F a b) (stepRoot₃_sq_iterated a b c)
    (stepRoot₁_generates F a) (stepRoot₃_generates F a b c)
    (le_of_eq (finrank₁₂ F a b c (by norm_num) hind))
    (nonsquare_ne_zero hind.first) (nonsquare_ne_zero hind.third) ha hb hc

/-- The third radicand has a simple zero and the other two are units. -/
theorem ramificationIndex_eq_two_001 (a b c : F)
    (hind : IndependentSquareclasses F a b c) (w : Place K (third F a b c))
    (ha : (w.restrict F).ord a = 0) (hb : (w.restrict F).ord b = 0)
    (hc : (w.restrict F).ord c = 1) : w.ramificationIndex F = 2 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  exact ThreeQuadraticPatterns.ramificationIndex_eq_two_001 w
    (stepRoot₁_sq F a) (stepRoot₂_sq F a b) (stepRoot₃_sq_iterated a b c)
    (stepRoot₁_generates F a) (stepRoot₂_generates F a b)
    (le_of_eq (finrank₂₃ F a b c (by norm_num) hind))
    (nonsquare_ne_zero hind.first) (nonsquare_ne_zero hind.second) ha hb hc

/-- A common base element of half the three radicand orders makes the whole
extension unramified. This includes negative orders, as needed at infinity. -/
theorem ramificationIndex_eq_one_of_common_twice (a b c : F)
    (hind : IndependentSquareclasses F a b c) (w : Place K (third F a b c))
    {t : F} (ht : t ≠ 0)
    (haord : (w.restrict F).ord a = 2 * (w.restrict F).ord t)
    (hbord : (w.restrict F).ord b = 2 * (w.restrict F).ord t)
    (hcord : (w.restrict F).ord c = 2 * (w.restrict F).ord t) :
    w.ramificationIndex F = 1 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have ha : a ≠ 0 := nonsquare_ne_zero hind.first
  have hb : b ≠ 0 := nonsquare_ne_zero hind.second
  have hc : c ≠ 0 := nonsquare_ne_zero hind.third
  have h₁ : (w.restrict (first F a)).ramificationIndex F = 1 := by
    apply QuadraticRescaledUnit.ramificationIndex_eq_one_of_ord_eq_twice
      (w.restrict (first F a)) (stepRoot₁_sq F a) (stepRoot₁_generates F a) ha ht
    simpa only [PlaceTower.restrict_restrict] using haord
  have hb₁ : (w.restrict (first F a)).ord (algebraMap F (first F a) b) =
      2 * (w.restrict (first F a)).ord (algebraMap F (first F a) t) := by
    rw [(w.restrict (first F a)).ord_restrict b,
      (w.restrict (first F a)).ord_restrict t]
    simp only [PlaceTower.restrict_restrict]
    rw [hbord]
    ring
  have h₂ : (w.restrict (second F a b)).ramificationIndex (first F a) = 1 := by
    apply QuadraticRescaledUnit.ramificationIndex_eq_one_of_ord_eq_twice
      (w.restrict (second F a b)) (stepRoot₂_sq F a b) (stepRoot₂_generates F a b)
      ((map_ne_zero (algebraMap F (first F a))).mpr hb)
      ((map_ne_zero (algebraMap F (first F a))).mpr ht)
    simpa only [PlaceTower.restrict_restrict] using hb₁
  have hc₂ : (w.restrict (second F a b)).ord (algebraMap F (second F a b) c) =
      2 * (w.restrict (second F a b)).ord (algebraMap F (second F a b) t) := by
    rw [(w.restrict (second F a b)).ord_restrict c,
      (w.restrict (second F a b)).ord_restrict t]
    simp only [PlaceTower.restrict_restrict]
    rw [hcord]
    ring
  have h₃ : w.ramificationIndex (second F a b) = 1 :=
    QuadraticRescaledUnit.ramificationIndex_eq_one_of_ord_eq_twice w
      (stepRoot₃_sq F a b c) (stepRoot₃_generates F a b c)
      ((map_ne_zero (algebraMap F (second F a b))).mpr hc)
      ((map_ne_zero (algebraMap F (second F a b))).mpr ht) hc₂
  rw [PlaceTower.ramificationIndex_mul_three (E := first F a) (L := second F a b),
    h₁, h₂, h₃]

/-- The all-unit finite-place pattern is unramified in the actual extension. -/
theorem ramificationIndex_eq_one_of_orders_zero (a b c : F)
    (hind : IndependentSquareclasses F a b c) (w : Place K (third F a b c))
    (ha : (w.restrict F).ord a = 0) (hb : (w.restrict F).ord b = 0)
    (hc : (w.restrict F).ord c = 0) : w.ramificationIndex F = 1 := by
  apply ramificationIndex_eq_one_of_common_twice a b c hind w (t := 1) one_ne_zero
  · simpa using ha
  · simpa using hb
  · simpa using hc

end FourCorner.Multiquadratic.Ramification

#print axioms FourCorner.Multiquadratic.Ramification.ramificationIndex_eq_two_100
#print axioms FourCorner.Multiquadratic.Ramification.ramificationIndex_eq_two_010
#print axioms FourCorner.Multiquadratic.Ramification.ramificationIndex_eq_two_001
#print axioms FourCorner.Multiquadratic.Ramification.ramificationIndex_eq_one_of_common_twice
#print axioms FourCorner.Multiquadratic.Ramification.ramificationIndex_eq_one_of_orders_zero
