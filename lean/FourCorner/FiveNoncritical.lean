import FourCorner.PairOddFactors
import FourCorner.FiveResidue
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace FourCorner
namespace IntegralModel

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- When five divides the side and misses the coordinate product, it divides
all four actual radii. -/
theorem five_dvd_radii (M : IntegralModel)
    (hL : (5 : ℤ) ∣ M.L) (hXY : ¬ (5 : ℤ) ∣ M.X * M.Y) :
    (5 : ℤ) ∣ M.A₀ ∧ (5 : ℤ) ∣ M.A₁ ∧
    (5 : ℤ) ∣ M.A₂ ∧ (5 : ℤ) ∣ M.A₃ := by
  have hX : (M.X : ZMod 5) ≠ 0 := by
    intro h
    exact hXY (dvd_mul_of_dvd_left
      ((ZMod.intCast_zmod_eq_zero_iff_dvd M.X 5).mp h) _)
  have hY : (M.Y : ZMod 5) ≠ 0 := by
    intro h
    exact hXY (dvd_mul_of_dvd_right
      ((ZMod.intCast_zmod_eq_zero_iff_dvd M.Y 5).mp h) _)
  have l0 : (M.L : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd M.L 5).mpr hL
  have e₀ := congrArg (fun z : ℤ => (z : ZMod 5)) M.sq₀
  have e₁ := congrArg (fun z : ℤ => (z : ZMod 5)) M.sq₁
  have e₂ := congrArg (fun z : ℤ => (z : ZMod 5)) M.sq₂
  have e₃ := congrArg (fun z : ℤ => (z : ZMod 5)) M.sq₃
  push_cast at e₀ e₁ e₂ e₃
  simp only [l0, zero_sub, neg_sq] at e₁ e₂ e₃
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd M.A₀ 5).mp
      (five_square_sum_units_zero _ _ _ hX hY e₀),
    (ZMod.intCast_zmod_eq_zero_iff_dvd M.A₁ 5).mp
      (five_square_sum_units_zero _ _ _ hX hY e₁),
    (ZMod.intCast_zmod_eq_zero_iff_dvd M.A₂ 5).mp
      (five_square_sum_units_zero _ _ _ hX hY e₂),
    (ZMod.intCast_zmod_eq_zero_iff_dvd M.A₃ 5).mp
      (five_square_sum_units_zero _ _ _ hX hY e₃)⟩

/-- The five obstruction persists after removing the entire common square
content. Its proof compares all four reduced square residues. -/
theorem five_dvd_reducedSide_of_dvd_content (M : IntegralModel)
    (hG : 5 ∣ M.radiusContent) : (5 : ℤ) ∣ M.reducedSide := by
  by_contra hH
  have hH0 : (M.reducedSide : ZMod 5) ≠ 0 := by
    intro he
    exact hH ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp he)
  let r : Fin 4 → ZMod 5 := fun i =>
    ((M.pairRadius i / (M.radiusContent : ℤ) : ℤ) : ZMod 5)
  apply five_four_squares_not_injective r
  intro i j he
  by_contra hij
  have hF := M.radiusContent_prime_pairDifferenceFactor_ne_zero (by decide : Nat.Prime 5) hG hij
  have hg : (M.radiusContent : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt M.radiusContent_pos)
  have hd := div_square_sub_div_square hg (M.radiusContent_dvd_pairRadius j)
    (M.radiusContent_dvd_pairRadius i) M.radiusContent_sq_dvd_L
    (M.pairRadius_sq_sub i j)
  have hd' := congrArg (fun z : ℤ => (z : ZMod 5)) hd
  push_cast at hd'
  change (r j)^2 - (r i)^2 = (M.reducedSide : ZMod 5) *
    (M.pairDifferenceFactor i j : ZMod 5) at hd'
  change (r i)^2 = (r j)^2 at he
  rw [he, sub_self] at hd'
  exact (mul_ne_zero hH0 hF) hd'.symm

private theorem five_value_pos_of_dvd {a : ℤ} (ha : a ≠ 0) (hd : (5 : ℤ) ∣ a) :
    1 ≤ padicValInt 5 a := by
  exact ((padicValInt_dvd_iff 1 a).mp (by simpa using hd)).resolve_left ha

private theorem five_value_radius_eq_content (M : IntegralModel) {a : ℤ}
    (ha : 0 < a) (hd : (M.radiusContent : ℤ) ∣ a)
    (hu : ¬ (5 : ℤ) ∣ a / (M.radiusContent : ℤ)) :
    padicValInt 5 a = padicValInt 5 (M.radiusContent : ℤ) := by
  have hg : (M.radiusContent : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt M.radiusContent_pos)
  have hq : a / (M.radiusContent : ℤ) ≠ 0 := by
    intro he
    have hm := Int.mul_ediv_cancel' hd
    rw [he, mul_zero] at hm
    exact (ne_of_gt ha) hm.symm
  calc
    padicValInt 5 a = padicValInt 5 ((M.radiusContent : ℤ) *
        (a / (M.radiusContent : ℤ))) := congrArg _ (Int.mul_ediv_cancel' hd).symm
    _ = padicValInt 5 (M.radiusContent : ℤ) := by
      rw [padicValInt.mul hg hq, padicValInt.eq_zero_of_not_dvd hu, add_zero]

/-- The local five-prime conclusion of Proposition int:five-depth on the
actual primitive integral model. Both valuations are unrestricted. -/
theorem five_noncritical (M : IntegralModel)
    (hL : (5 : ℤ) ∣ M.L) (hXY : ¬ (5 : ℤ) ∣ M.X * M.Y) :
    1 ≤ padicValInt 5 (M.radiusContent : ℤ) ∧
    2 * padicValInt 5 (M.radiusContent : ℤ) < padicValInt 5 M.L ∧
    padicValInt 5 M.A₀ = padicValInt 5 (M.radiusContent : ℤ) ∧
    padicValInt 5 M.A₁ = padicValInt 5 (M.radiusContent : ℤ) ∧
    padicValInt 5 M.A₂ = padicValInt 5 (M.radiusContent : ℤ) ∧
    padicValInt 5 M.A₃ = padicValInt 5 (M.radiusContent : ℤ) := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := M.five_dvd_radii hL hXY
  have hG : 5 ∣ M.radiusContent := by
    apply (M.dvd_radiusContent_iff 5).mpr
    intro i
    fin_cases i <;> simp_all [pairRadius]
  have hH := M.five_dvd_reducedSide_of_dvd_content hG
  have hg : (M.radiusContent : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt M.radiusContent_pos)
  have hHn := ne_of_gt M.reducedSide_pos
  have hvH := five_value_pos_of_dvd hHn hH
  have hvL := congrArg (padicValInt 5) M.reducedSide_factorization
  rw [padicValInt.mul (pow_ne_zero 2 hg) hHn] at hvL
  have hvsq : padicValInt 5 ((M.radiusContent : ℤ)^2) =
      2 * padicValInt 5 (M.radiusContent : ℤ) := by
    simp only [padicValInt, Int.natAbs_pow, padicValNat.pow]
  rw [hvsq] at hvL
  obtain ⟨u₀, u₁, u₂, u₃⟩ := M.normalized_radii_units (by decide : Nat.Prime 5) hH
  exact ⟨five_value_pos_of_dvd hg (Int.natCast_dvd_natCast.mpr hG), by omega,
    M.five_value_radius_eq_content M.A₀_pos M.radiusContent_dvd₀ u₀,
    M.five_value_radius_eq_content M.A₁_pos M.radiusContent_dvd₁ u₁,
    M.five_value_radius_eq_content M.A₂_pos M.radiusContent_dvd₂ u₂,
    M.five_value_radius_eq_content M.A₃_pos M.radiusContent_dvd₃ u₃⟩

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.five_dvd_radii
#print axioms FourCorner.IntegralModel.five_dvd_reducedSide_of_dvd_content
#print axioms FourCorner.IntegralModel.five_noncritical
