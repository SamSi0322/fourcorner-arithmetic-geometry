import FourCorner.ContentCenterIdentity
import FourCorner.CriticalSeventeenActual

namespace FourCorner.IntegralModel

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- If the reduced side is divisible by seventeen, the normalized center norm
is a unit, so its valuation comes entirely from the common radius content. -/
theorem seventeen_center_valuation_of_dvd_reducedSide (M : IntegralModel)
    (hH : (17 : ℤ) ∣ M.reducedSide) :
    padicValInt 17 ((2 * M.X - M.L)^2 + (2 * M.Y - M.L)^2) =
      2 * padicValNat 17 M.radiusContent := by
  let K : ℤ := 4 * (M.A₀ / (M.radiusContent : ℤ))^2 -
    4 * M.reducedSide * (M.X + M.Y) +
    2 * (M.radiusContent : ℤ)^2 * M.reducedSide^2
  have ha : ((M.A₀ / (M.radiusContent : ℤ) : ℤ) : ZMod 17) ≠ 0 := by
    intro hz
    exact (M.normalized_radii_units (by decide : Nat.Prime 17) hH).1
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mp hz)
  have hh : (M.reducedSide : ZMod 17) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mpr hH
  have hK : ¬ (17 : ℤ) ∣ K := by
    intro hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd K 17).mpr hd
    dsimp [K] at hz
    push_cast at hz
    rw [hh] at hz
    have he : (4 : ZMod 17) * ((M.A₀ / (M.radiusContent : ℤ) : ℤ) : ZMod 17)^2 = 0 := by
      simpa using hz
    exact (mul_ne_zero (by decide) (pow_ne_zero 2 ha)) he
  have hK0 : K ≠ 0 := by
    intro he
    exact hK (he ▸ dvd_zero 17)
  have hG0 : (M.radiusContent : ℤ) ≠ 0 := by
    exact_mod_cast M.radiusContent_pos.ne'
  rw [M.content_center_identity]
  change padicValInt 17 ((M.radiusContent : ℤ)^2 * K) = _
  rw [padicValInt.mul (pow_ne_zero 2 hG0) hK0,
    padicValInt.eq_zero_of_not_dvd hK, add_zero]
  simp only [padicValInt, Int.natAbs_pow, Int.natAbs_natCast, padicValNat.pow]

/-- The noncritical center valuation for a seventeen-prime content divisor. -/
theorem noncritical_seventeen_center_valuation (M : IntegralModel)
    (_hG : 17 ∣ M.radiusContent) (hH : (17 : ℤ) ∣ M.reducedSide) :
    padicValInt 17 ((2 * M.X - M.L)^2 + (2 * M.Y - M.L)^2) =
      2 * padicValNat 17 M.radiusContent :=
  M.seventeen_center_valuation_of_dvd_reducedSide hH

end FourCorner.IntegralModel

#print axioms FourCorner.IntegralModel.seventeen_center_valuation_of_dvd_reducedSide
#print axioms FourCorner.IntegralModel.noncritical_seventeen_center_valuation
