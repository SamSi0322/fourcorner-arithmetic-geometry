import FourCorner.CriticalSeventeenActual
import FourCorner.CriticalSeventeenFinite

namespace FourCorner.IntegralModel

/-- In the actual critical pattern, opposite normalized square radii cancel. -/
theorem critical_seventeen_opposite_squares (M : IntegralModel)
    (hG : 17 ∣ M.radiusContent)
    (hcrit : padicValInt 17 M.L = 2 * padicValNat 17 M.radiusContent) :
    (17 : ℤ) ∣ (M.criticalReducedRadius 0)^2 + (M.criticalReducedRadius 3)^2 ∧
    (17 : ℤ) ∣ (M.criticalReducedRadius 1)^2 + (M.criticalReducedRadius 2)^2 := by
  obtain ⟨hi, hb, h1, h2, h3⟩ := M.critical_seventeen_square_pattern hG hcrit
  obtain ⟨_, _, _, _, _, _, h03, h12, _⟩ := FourCorner.seventeen_square_pattern
    (M.criticalReducedRadius 0) (M.criticalReducedRadius 1)
    (M.criticalReducedRadius 2) (M.criticalReducedRadius 3)
    M.criticalIota17 M.criticalShift17 hi hb h1 h2 h3
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mp
    push_cast
    exact h03
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mp
    push_cast
    exact h12

/-- A second exact center identity expresses the bracket using opposite radii. -/
theorem criticalReducedRadius_center_identity (M : IntegralModel) :
    (2 * M.X - M.L)^2 + (2 * M.Y - M.L)^2 =
      (M.radiusContent : ℤ)^2 *
        (2 * ((M.criticalReducedRadius 0)^2 + (M.criticalReducedRadius 3)^2) -
          2 * (M.radiusContent : ℤ)^2 * M.reducedSide^2) := by
  have ha0 : (M.radiusContent : ℤ) * M.criticalReducedRadius 0 = M.A₀ :=
    Int.mul_ediv_cancel' M.radiusContent_dvd₀
  have ha3 : (M.radiusContent : ℤ) * M.criticalReducedRadius 3 = M.A₃ :=
    Int.mul_ediv_cancel' M.radiusContent_dvd₃
  calc
    (2 * M.X - M.L)^2 + (2 * M.Y - M.L)^2 =
        2 * (M.A₀^2 + M.A₃^2) - 2 * M.L^2 := by
      nlinarith [M.sq₀, M.sq₃]
    _ = 2 * (((M.radiusContent : ℤ) * M.criticalReducedRadius 0)^2 +
        ((M.radiusContent : ℤ) * M.criticalReducedRadius 3)^2) -
        2 * ((M.radiusContent : ℤ)^2 * M.reducedSide)^2 := by
      rw [ha0, ha3, M.reducedSide_factorization]
    _ = _ := by ring

/-- At critical seventeen, the center norm gains one further power beyond the
square of the exact radius-content prime power. -/
theorem critical_seventeen_center_divisibility (M : IntegralModel)
    (hG : 17 ∣ M.radiusContent)
    (hcrit : padicValInt 17 M.L = 2 * padicValNat 17 M.radiusContent) :
    (17 : ℤ)^(2 * padicValNat 17 M.radiusContent + 1) ∣
      (2 * M.X - M.L)^2 + (2 * M.Y - M.L)^2 := by
  have h03 := (M.critical_seventeen_opposite_squares hG hcrit).1
  have hg : (17 : ℤ) ∣ (M.radiusContent : ℤ) := Int.natCast_dvd_natCast.mpr hG
  have hg2 : (17 : ℤ) ∣ (M.radiusContent : ℤ)^2 := dvd_pow hg (by decide)
  have hbracket : (17 : ℤ) ∣
      2 * ((M.criticalReducedRadius 0)^2 + (M.criticalReducedRadius 3)^2) -
        2 * (M.radiusContent : ℤ)^2 * M.reducedSide^2 :=
    dvd_sub (dvd_mul_of_dvd_right h03 2)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hg2 2) _)
  have hp : (17 : ℤ)^padicValNat 17 M.radiusContent ∣ (M.radiusContent : ℤ) := by
    simpa using (padicValInt_dvd (p := 17) (M.radiusContent : ℤ))
  have hp2 : (17 : ℤ)^(2 * padicValNat 17 M.radiusContent) ∣
      (M.radiusContent : ℤ)^2 := by
    simpa only [← pow_mul, Nat.mul_comm] using pow_dvd_pow_of_dvd hp 2
  rw [M.criticalReducedRadius_center_identity, pow_add, pow_one]
  exact mul_dvd_mul hp2 hbracket

end FourCorner.IntegralModel

#print axioms FourCorner.IntegralModel.critical_seventeen_opposite_squares
#print axioms FourCorner.IntegralModel.critical_seventeen_center_divisibility
