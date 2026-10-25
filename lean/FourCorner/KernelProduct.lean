import FourCorner.GaussianKernel
import FourCorner.IntegralNormalization
import FourCorner.KernelStrict
import FourCorner.KernelGaussianAlgebra
import FourCorner.RationalSquarefreeKernel

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace FourCorner.IntegralModel

/-- The sum of the products of the two pairs of opposite normalized radii. -/
def oppositeProductSum (M : IntegralModel) : ℚ :=
  (M.A₀ : ℚ) / M.L * ((M.A₃ : ℚ) / M.L) +
    (M.A₁ : ℚ) / M.L * ((M.A₂ : ℚ) / M.L)

/-- Multiplying the actual corner roots retains their common source and labels. -/
theorem corner_product_gaussian_root (M : IntegralModel) (hX : Odd M.X) :
    ∃ q : GaussianInt, q ≠ 0 ∧
      (⟨M.X, M.Y⟩ : GaussianInt) * ⟨M.X - M.L, M.Y - M.L⟩ *
        (⟨M.X - M.L, M.Y⟩ * ⟨M.X, M.Y - M.L⟩) =
      (M.cornerKernel : GaussianInt) * q ^ 2 := by
  have hL : Even M.L := even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  obtain ⟨q₀, hq₀, h₀, _, _⟩ := M.corner_gaussian_root hX hL (false, false)
  obtain ⟨q₁, hq₁, h₁, _, _⟩ := M.corner_gaussian_root hX hL (true, false)
  obtain ⟨q₂, hq₂, h₂, _, _⟩ := M.corner_gaussian_root hX hL (false, true)
  obtain ⟨q₃, hq₃, h₃, _, _⟩ := M.corner_gaussian_root hX hL (true, true)
  simp only [cornerX, cornerY, Bool.false_eq_true, ↓reduceIte, sub_zero] at h₀ h₁ h₂ h₃
  refine ⟨q₀ * q₁ * q₂ * q₃, mul_ne_zero (mul_ne_zero (mul_ne_zero hq₀ hq₁) hq₂) hq₃, ?_⟩
  rw [h₀, h₁, h₂, h₃]
  simp only [cornerKernel, Nat.cast_mul]
  ring

/-- The product of the two opposite Gaussian displacement pairs has precisely
 the canonical squareclass n, in rational coordinates. -/
theorem opposite_product_gaussian_class (M : IntegralModel) (hX : Odd M.X) :
    let x := (M.X : ℚ) / M.L
    let y := (M.Y : ℚ) / M.L
    let u := (x - y) * (x + y - 1)
    let v := 2 * x * y - x - y
    GaussianRationalSquareClass (u ^ 2 - v * (v + 1)) (u * (2 * v + 1))
      (M.cornerKernel : ℚ) := by
  dsimp
  obtain ⟨q, hq, hprod⟩ := M.corner_product_gaussian_root hX
  have hL : (M.L : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt M.L_pos)
  have hn : (M.cornerKernel : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt M.cornerKernel_pos)
  have hre := congrArg Zsqrtd.re hprod
  have him := congrArg Zsqrtd.im hprod
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul,
    Zsqrtd.re_natCast, Zsqrtd.im_natCast, pow_two] at hre him
  refine ⟨hn, (q.re : ℚ) / (M.L : ℚ) ^ 2, (q.im : ℚ) / (M.L : ℚ) ^ 2, ?_, ?_, ?_⟩
  · by_contra hz
    push Not at hz
    have hqr : q.re = 0 := by exact_mod_cast (div_eq_zero_iff.mp hz.1).resolve_right (pow_ne_zero 2 hL)
    have hqi : q.im = 0 := by exact_mod_cast (div_eq_zero_iff.mp hz.2).resolve_right (pow_ne_zero 2 hL)
    exact hq (Zsqrtd.ext hqr hqi)
  · have hh := hre
    have hhQ := congrArg (fun z : ℤ => (z : ℚ)) hh
    push_cast at hhQ
    field_simp
    linear_combination hhQ
  · have hhQ := congrArg (fun z : ℤ => (z : ℚ)) him
    push_cast at hhQ
    field_simp
    linear_combination hhQ

/-- Strictness of the actual kernel parameter follows from the original
rational-distance point, with no additional diagonal hypothesis. -/
theorem oppositeProductSum_gt_one (M : IntegralModel) : 1 < M.oppositeProductSum :=
  strict_point_kernel_gt_one M.toStrictPoint

/-- The canonical corner kernel is exactly the rational squareclass of t²−1.
The Gaussian product root is constructed from all four actual corner roots. -/
theorem canonical_kernel_product (M : IntegralModel) (hX : Odd M.X) :
    1 < M.oppositeProductSum ∧
    ∃ w : ℚ, 0 < w ∧ M.oppositeProductSum ^ 2 - 1 = (M.cornerKernel : ℚ) * w ^ 2 := by
  have ht := M.oppositeProductSum_gt_one
  refine ⟨ht, ?_⟩
  let x := (M.X : ℚ) / M.L
  let y := (M.Y : ℚ) / M.L
  let u := (x - y) * (x + y - 1)
  let v := 2 * x * y - x - y
  let a := (M.A₀ : ℚ) / M.L * ((M.A₃ : ℚ) / M.L)
  let b := (M.A₁ : ℚ) / M.L * ((M.A₂ : ℚ) / M.L)
  have hs := M.toStrictPoint
  obtain ⟨_, _, _, _, _, _, _, _, hf⟩ := hs
  obtain ⟨ha, hb⟩ := four_squares_opposite_products hf
  have hp := M.opposite_product_gaussian_class hX
  change GaussianRationalSquareClass (u ^ 2 - v * (v + 1)) (u * (2 * v + 1))
    (M.cornerKernel : ℚ) at hp
  obtain ⟨_, rr, ri, hR, hre, him⟩ := hp
  have hspos : 0 < (a + b) ^ 2 - 1 := by
    change 1 < a + b at ht
    nlinarith
  exact vertical_gaussian_squareclass_transfer u v a b (M.cornerKernel : ℚ) rr ri
    ha hb (by exact_mod_cast M.cornerKernel_pos) hspos hR hre (by nlinarith [him])

/-- Literal canonical-kernel identification in Proposition int:kernel-product.
The rational squarefree part uses the numerator times the positive denominator. -/
theorem cornerKernel_eq_rational_squarefreePart (M : IntegralModel) (hX : Odd M.X) :
    M.cornerKernel = rationalSquarefreePart (M.oppositeProductSum ^ 2 - 1) := by
  obtain ⟨ht, w, hw, h⟩ := M.canonical_kernel_product hX
  exact (rationalSquarefreePart_eq_of_decomposition (by nlinarith) M.cornerKernel_squarefree hw h).symm

/-- The complete manuscript proposition, including t>1, an actual positive
rational square witness, and equality of the canonical squarefree kernels. -/
theorem kernel_product (M : IntegralModel) (hX : Odd M.X) :
    1 < M.oppositeProductSum ∧
    (∃ w : ℚ, 0 < w ∧ M.oppositeProductSum ^ 2 - 1 = (M.cornerKernel : ℚ) * w ^ 2) ∧
    M.cornerKernel = rationalSquarefreePart (M.oppositeProductSum ^ 2 - 1) := by
  obtain ⟨ht, hw⟩ := M.canonical_kernel_product hX
  exact ⟨ht, hw, M.cornerKernel_eq_rational_squarefreePart hX⟩

end FourCorner.IntegralModel

#print axioms FourCorner.IntegralModel.corner_product_gaussian_root
#print axioms FourCorner.IntegralModel.opposite_product_gaussian_class
#print axioms FourCorner.IntegralModel.oppositeProductSum_gt_one
#print axioms FourCorner.IntegralModel.canonical_kernel_product

#print axioms FourCorner.IntegralModel.cornerKernel_eq_rational_squarefreePart
#print axioms FourCorner.IntegralModel.kernel_product
