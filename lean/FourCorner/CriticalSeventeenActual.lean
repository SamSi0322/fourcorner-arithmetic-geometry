import FourCorner.PairOddFactors
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace FourCorner
namespace IntegralModel

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The actual radii divided by their common integral content. -/
def criticalReducedRadius (M : IntegralModel) (i : Fin 4) : ℤ :=
  M.pairRadius i / (M.radiusContent : ℤ)

/-- The distinguished square root of minus one from the actual coordinates. -/
def criticalIota17 (M : IntegralModel) : ZMod 17 := (M.Y : ZMod 17) / (M.X : ZMod 17)

/-- The horizontal normalized square difference at the critical prime. -/
def criticalShift17 (M : IntegralModel) : ZMod 17 :=
  -2 * (M.reducedSide : ZMod 17) * (M.X : ZMod 17)

/-- Exact content division in all the squared radius differences. -/
theorem criticalReducedRadius_sq_sub (M : IntegralModel) (i j : Fin 4) :
    (M.criticalReducedRadius j)^2 - (M.criticalReducedRadius i)^2 =
      M.reducedSide * M.pairDifferenceFactor i j := by
  exact div_square_sub_div_square (by exact_mod_cast M.radiusContent_pos.ne')
    (M.radiusContent_dvd_pairRadius j) (M.radiusContent_dvd_pairRadius i)
    M.radiusContent_sq_dvd_L (M.pairRadius_sq_sub i j)

/-- Exact critical valuation forces the reduced side to be a prime unit. -/
theorem critical_prime_not_dvd_reducedSide (M : IntegralModel) {p : ℕ}
    (hp : p.Prime)
    (hcrit : padicValInt p M.L = 2 * padicValNat p M.radiusContent) :
    ¬ (p : ℤ) ∣ M.reducedSide := by
  let : Fact p.Prime := ⟨hp⟩
  have hfac := congrArg (fun z : ℤ => padicValInt p z) M.reducedSide_factorization
  have hG : (M.radiusContent : ℤ) ≠ 0 := by exact_mod_cast M.radiusContent_pos.ne'
  have hH : M.reducedSide ≠ 0 := M.reducedSide_pos.ne'
  rw [padicValInt.mul (pow_ne_zero 2 hG) hH] at hfac
  have hGval : padicValInt p ((M.radiusContent : ℤ)^2) =
      2 * padicValNat p M.radiusContent := by
    simp only [padicValInt, Int.natAbs_pow, Int.natAbs_natCast, padicValNat.pow]
  rw [hGval, hcrit] at hfac
  have hz : padicValInt p M.reducedSide = 0 := by omega
  exact ((padicValInt.eq_zero_iff.mp hz).resolve_left hp.ne_one).resolve_left hH

/-- Coordinate units and their norm relation come from the actual origin radius. -/
theorem critical_seventeen_coordinate_data (M : IntegralModel)
    (hG : 17 ∣ M.radiusContent) :
    (M.X : ZMod 17) ≠ 0 ∧ (M.Y : ZMod 17) ≠ 0 ∧
      (M.L : ZMod 17) = 0 ∧ (M.X : ZMod 17)^2 + (M.Y : ZMod 17)^2 = 0 := by
  have pg : (17 : ℤ) ∣ (M.radiusContent : ℤ) := Int.natCast_dvd_natCast.mpr hG
  have h₀ := dvd_trans pg M.radiusContent_dvd₀
  have h₁ := dvd_trans pg M.radiusContent_dvd₁
  have h₂ := dvd_trans pg M.radiusContent_dvd₂
  have h₃ := dvd_trans pg M.radiusContent_dvd₃
  obtain ⟨hl, hx, hy, _⟩ := M.common_radius_prime_support (by decide : Nat.Prime 17)
    (by decide) h₀ h₁ h₂ h₃
  have ha : (M.A₀ : ZMod 17) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd M.A₀ 17).mpr h₀
  refine ⟨?_, ?_, (ZMod.intCast_zmod_eq_zero_iff_dvd M.L 17).mpr hl, ?_⟩
  · exact fun h => hx ((ZMod.intCast_zmod_eq_zero_iff_dvd M.X 17).mp h)
  · exact fun h => hy ((ZMod.intCast_zmod_eq_zero_iff_dvd M.Y 17).mp h)
  · have h := congrArg (fun z : ℤ => (z : ZMod 17)) M.sq₀
    push_cast at h
    simpa [ha] using h.symm

/-- The actual coordinate ratio is a square root of minus one at 17. -/
theorem criticalIota17_sq (M : IntegralModel) (hG : 17 ∣ M.radiusContent) :
    M.criticalIota17^2 = -1 := by
  obtain ⟨hx, _, _, he⟩ := M.critical_seventeen_coordinate_data hG
  dsimp [criticalIota17]
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 hx)).mpr
  linear_combination he

/-- The actual normalized horizontal step is nonzero in the critical case. -/
theorem criticalShift17_ne_zero (M : IntegralModel) (hG : 17 ∣ M.radiusContent)
    (hcrit : padicValInt 17 M.L = 2 * padicValNat 17 M.radiusContent) :
    M.criticalShift17 ≠ 0 := by
  have hx := (M.critical_seventeen_coordinate_data hG).1
  have hH : (M.reducedSide : ZMod 17) ≠ 0 := by
    intro h
    exact M.critical_prime_not_dvd_reducedSide (by decide : Nat.Prime 17) hcrit
      ((ZMod.intCast_zmod_eq_zero_iff_dvd M.reducedSide 17).mp h)
  exact mul_ne_zero (mul_ne_zero (by decide) hH) hx

/-- All three square-pattern identities are obtained from the actual integer radii. -/
theorem critical_seventeen_square_pattern (M : IntegralModel)
    (hG : 17 ∣ M.radiusContent)
    (hcrit : padicValInt 17 M.L = 2 * padicValNat 17 M.radiusContent) :
    M.criticalIota17^2 = -1 ∧ M.criticalShift17 ≠ 0 ∧
    (M.criticalReducedRadius 1 : ZMod 17)^2 =
      (M.criticalReducedRadius 0 : ZMod 17)^2 + M.criticalShift17 ∧
    (M.criticalReducedRadius 2 : ZMod 17)^2 =
      (M.criticalReducedRadius 0 : ZMod 17)^2 + M.criticalIota17 * M.criticalShift17 ∧
    (M.criticalReducedRadius 3 : ZMod 17)^2 =
      (M.criticalReducedRadius 0 : ZMod 17)^2 + (1 + M.criticalIota17) * M.criticalShift17 := by
  obtain ⟨hx, _, hl, _⟩ := M.critical_seventeen_coordinate_data hG
  have h₁ := congrArg (fun z : ℤ => (z : ZMod 17)) (M.criticalReducedRadius_sq_sub 0 1)
  have h₂ := congrArg (fun z : ℤ => (z : ZMod 17)) (M.criticalReducedRadius_sq_sub 0 2)
  have h₃ := congrArg (fun z : ℤ => (z : ZMod 17)) (M.criticalReducedRadius_sq_sub 0 3)
  simp [pairDifferenceFactor] at h₁ h₂ h₃
  rw [hl] at h₁ h₂ h₃
  refine ⟨M.criticalIota17_sq hG, M.criticalShift17_ne_zero hG hcrit, ?_, ?_, ?_⟩
  · dsimp [criticalShift17]
    linear_combination h₁
  · dsimp [criticalIota17, criticalShift17]
    field_simp [hx]
    linear_combination h₂
  · dsimp [criticalIota17, criticalShift17]
    field_simp [hx]
    linear_combination h₃

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.critical_seventeen_square_pattern
