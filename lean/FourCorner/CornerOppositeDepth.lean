import FourCorner.PairSupport
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace FourCorner
namespace IntegralModel

/-- The squared-radius difference of an opposite pair has an odd geometric
factor after removing `2L`, in either ordering of the pair. -/
theorem opposite_square_difference_odd_factor (M : IntegralModel)
    {c d : Bool × Bool} (he : c.1 ≠ d.1) (hf : c.2 ≠ d.2) :
    ∃ f : ℤ, f % 2 = 1 ∧ M.cornerRadius c ^ 2 - M.cornerRadius d ^ 2 = 2 * M.L * f := by
  obtain ⟨hL, hor⟩ := M.basic_mod_four
  rcases c with ⟨ce, cf⟩
  rcases d with ⟨de, df⟩
  cases ce <;> cases cf <;> cases de <;> cases df <;>
    simp only [ne_eq, not_true_eq_false] at he hf
  all_goals simp only [cornerRadius]
  · refine ⟨M.X + M.Y - M.L, by omega, ?_⟩
    rw [M.sq₀, M.sq₃]
    ring
  · refine ⟨M.X - M.Y, by omega, ?_⟩
    rw [M.sq₂, M.sq₁]
    ring
  · refine ⟨M.Y - M.X, by omega, ?_⟩
    rw [M.sq₁, M.sq₂]
    ring
  · refine ⟨M.L - M.X - M.Y, by omega, ?_⟩
    rw [M.sq₃, M.sq₀]
    ring

/-- The product of the actual half-sum and half-difference of opposite radii
has exactly one fewer factor of two than the side. -/
theorem opposite_half_product_two_depth (M : IntegralModel)
    {c d : Bool × Bool} (he : c.1 ≠ d.1) (hf : c.2 ≠ d.2) :
    padicValInt 2 (((M.cornerRadius c + M.cornerRadius d) / 2) *
      ((M.cornerRadius c - M.cornerRadius d) / 2)) = padicValInt 2 M.L - 1 := by
  obtain ⟨f, hfodd, hsq⟩ := M.opposite_square_difference_odd_factor he hf
  have hv := M.corner_pair_half_sum_integral c d
  have hc := Int.odd_iff.mp (M.corner_radius_odd c)
  have hd := Int.odd_iff.mp (M.corner_radius_odd d)
  have hdiff : 2 * ((M.cornerRadius c - M.cornerRadius d) / 2) =
      M.cornerRadius c - M.cornerRadius d := by
    apply Int.mul_ediv_cancel'
    exact Int.dvd_of_emod_eq_zero (by omega)
  have hprod : 2 * (((M.cornerRadius c + M.cornerRadius d) / 2) *
      ((M.cornerRadius c - M.cornerRadius d) / 2)) = M.L * f := by
    have hmul := congrArg₂ (fun x y : ℤ => x * y) hv hdiff
    nlinarith [hmul, hsq]
  have hf0 : f ≠ 0 := by omega
  have hL0 : M.L ≠ 0 := ne_of_gt M.L_pos
  have hVD0 : ((M.cornerRadius c + M.cornerRadius d) / 2) *
      ((M.cornerRadius c - M.cornerRadius d) / 2) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hprod
    exact (mul_ne_zero hL0 hf0) hprod.symm
  have hfval : padicValInt 2 f = 0 :=
    padicValInt.eq_zero_of_not_dvd (by
      intro h
      have hz := Int.emod_eq_zero_of_dvd h
      omega)
  have heq := congrArg (padicValInt 2) hprod
  rw [padicValInt.mul (by norm_num) hVD0,
    padicValInt.mul hL0 hf0, hfval] at heq
  have htwo : padicValInt 2 (2 : ℤ) = 1 := padicValInt.self (by decide)
  rw [htwo, add_zero] at heq
  exact (Nat.sub_eq_of_eq_add (heq.symm.trans (Nat.add_comm _ _))).symm

/-- The exact depth of an opposite half-product is at least two, since the
side of a primitive model is divisible by eight. -/
theorem opposite_half_product_two_depth_at_least_two (M : IntegralModel)
    {c d : Bool × Bool} (he : c.1 ≠ d.1) (hf : c.2 ≠ d.2) :
    2 ≤ padicValInt 2 (((M.cornerRadius c + M.cornerRadius d) / 2) *
      ((M.cornerRadius c - M.cornerRadius d) / 2)) := by
  rw [M.opposite_half_product_two_depth he hf]
  have h8 : (2 : ℤ) ^ 3 ∣ M.L := by
    norm_num
    exact Int.dvd_of_emod_eq_zero M.eight_divides_L
  have hv := ((padicValInt_dvd_iff 3 M.L).mp h8).resolve_left (ne_of_gt M.L_pos)
  exact Nat.sub_le_sub_right hv 1

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.opposite_square_difference_odd_factor
#print axioms FourCorner.IntegralModel.opposite_half_product_two_depth
#print axioms FourCorner.IntegralModel.opposite_half_product_two_depth_at_least_two
