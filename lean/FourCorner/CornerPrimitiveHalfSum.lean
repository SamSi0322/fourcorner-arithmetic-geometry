import FourCorner.RadiusContent
import FourCorner.PairSupport

set_option autoImplicit false

namespace FourCorner.IntegralModel

/-- The radius of the labelled corner after removing the actual common gcd
of all four integer radii. -/
def primitiveCornerRadius (M : IntegralModel) (c : Bool × Bool) : ℤ :=
  M.cornerRadius c / (M.radiusContent : ℤ)

/-- The half-sum of two radii after removal of their four-radius content. -/
def primitivePairHalfSum (M : IntegralModel) (c d : Bool × Bool) : ℤ :=
  (M.primitiveCornerRadius c + M.primitiveCornerRadius d) / 2

theorem radiusContent_dvd_cornerRadius (M : IntegralModel) (c : Bool × Bool) :
    (M.radiusContent : ℤ) ∣ M.cornerRadius c := by
  rcases c with ⟨e, f⟩
  cases e <;> cases f <;> simp only [cornerRadius]
  · exact M.radiusContent_dvd₀
  · exact M.radiusContent_dvd₂
  · exact M.radiusContent_dvd₁
  · exact M.radiusContent_dvd₃

theorem primitiveCornerRadius_factorization (M : IntegralModel) (c : Bool × Bool) :
    (M.radiusContent : ℤ) * M.primitiveCornerRadius c = M.cornerRadius c :=
  Int.mul_ediv_cancel' (M.radiusContent_dvd_cornerRadius c)

theorem primitiveCornerRadius_pos (M : IntegralModel) (c : Bool × Bool) :
    0 < M.primitiveCornerRadius c :=
  Int.ediv_pos_of_pos_of_dvd (M.cornerRadius_pos c) (Int.natCast_nonneg _)
    (M.radiusContent_dvd_cornerRadius c)

/-- Exact division of the odd original radius by its content retains oddness. -/
theorem primitiveCornerRadius_odd (M : IntegralModel) (c : Bool × Bool) :
    Odd (M.primitiveCornerRadius c) := by
  have h : Odd ((M.radiusContent : ℤ) * M.primitiveCornerRadius c) := by
    rw [M.primitiveCornerRadius_factorization c]
    exact M.corner_radius_odd c
  exact (Int.odd_mul.mp h).2

/-- The common content itself is odd, derived from an actual odd radius. -/
theorem radiusContent_isOdd (M : IntegralModel) : Odd M.radiusContent := by
  have h : Odd ((M.radiusContent : ℤ) * M.primitiveCornerRadius (false, false)) := by
    rw [M.primitiveCornerRadius_factorization]
    exact M.corner_radius_odd _
  exact_mod_cast (Int.odd_mul.mp h).1

/-- These are precisely the primitive radius quotients: their joint gcd is one. -/
theorem primitiveCornerRadii_gcd (M : IntegralModel) :
    gcd4 (M.primitiveCornerRadius (false, false)) (M.primitiveCornerRadius (true, false))
      (M.primitiveCornerRadius (false, true)) (M.primitiveCornerRadius (true, true)) = 1 := by
  simpa only [primitiveCornerRadius, cornerRadius] using M.normalized_radii_primitive

theorem primitivePairHalfSum_integral (M : IntegralModel) (c d : Bool × Bool) :
    2 * M.primitivePairHalfSum c d =
      M.primitiveCornerRadius c + M.primitiveCornerRadius d := by
  apply Int.mul_ediv_cancel'
  exact even_iff_two_dvd.mp
    ((M.primitiveCornerRadius_odd c).add_odd (M.primitiveCornerRadius_odd d))

theorem primitivePairHalfSum_pos (M : IntegralModel) (c d : Bool × Bool) :
    0 < M.primitivePairHalfSum c d := by
  have h := M.primitivePairHalfSum_integral c d
  have hc := M.primitiveCornerRadius_pos c
  have hd := M.primitiveCornerRadius_pos d
  omega

/-- The original half-sum is exactly the actual radius content times the
primitive half-sum; both divisions by two are exact integer divisions. -/
theorem primitivePairHalfSum_factorization (M : IntegralModel) (c d : Bool × Bool) :
    (M.cornerRadius c + M.cornerRadius d) / 2 =
      (M.radiusContent : ℤ) * M.primitivePairHalfSum c d := by
  have h := M.corner_pair_half_sum_integral c d
  have hp := M.primitivePairHalfSum_integral c d
  have hc := M.primitiveCornerRadius_factorization c
  have hd := M.primitiveCornerRadius_factorization d
  nlinarith

/-- The primitive half-sums inherit the full six-pair support theorem, with
the original canonical Gaussian colours unchanged. -/
theorem primitive_pair_half_sum_support (M : IntegralModel) (hX : Odd M.X)
    {c d : Bool × Bool} (hne : c ≠ d) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hV : (p : ℤ) ∣ M.primitivePairHalfSum c d) :
    (¬ p ∣ M.cornerClass c * M.cornerClass d) ∧
      legendreSym p (-((M.cornerClass c : ℤ) * M.cornerClass d)) = 1 := by
  apply M.six_pair_support hX hne hp2
  rw [M.primitivePairHalfSum_factorization]
  exact dvd_mul_of_dvd_right hV _

/-- The complete primitive-radius half-sum formulation: the content is the
actual four-radius gcd, the primitive radii are positive and odd, and every
odd prime in any of the six primitive half-sums has the same colour support. -/
theorem primitive_radius_half_sums (M : IntegralModel) (hX : Odd M.X) :
    Odd M.radiusContent ∧
    (∀ c, 0 < M.primitiveCornerRadius c ∧ Odd (M.primitiveCornerRadius c)) ∧
    (∀ c d, 0 < M.primitivePairHalfSum c d ∧
      2 * M.primitivePairHalfSum c d =
        M.primitiveCornerRadius c + M.primitiveCornerRadius d ∧
      (M.cornerRadius c + M.cornerRadius d) / 2 =
        (M.radiusContent : ℤ) * M.primitivePairHalfSum c d) ∧
    (∀ (c d : Bool × Bool), c ≠ d → ∀ (p : ℕ) [Fact p.Prime], Odd p →
      (p : ℤ) ∣ M.primitivePairHalfSum c d →
      (¬ p ∣ M.cornerClass c * M.cornerClass d) ∧
        legendreSym p (-((M.cornerClass c : ℤ) * M.cornerClass d)) = 1) := by
  refine ⟨M.radiusContent_isOdd,
    fun c => ⟨M.primitiveCornerRadius_pos c, M.primitiveCornerRadius_odd c⟩,
    fun c d => ⟨M.primitivePairHalfSum_pos c d, M.primitivePairHalfSum_integral c d,
      M.primitivePairHalfSum_factorization c d⟩, ?_⟩
  intro c d hne p hp hodd hV
  exact M.primitive_pair_half_sum_support hX hne
    (hodd.ne_two_of_dvd_nat (dvd_refl p)) hV

end FourCorner.IntegralModel

#print axioms FourCorner.IntegralModel.primitiveCornerRadius_odd
#print axioms FourCorner.IntegralModel.primitiveCornerRadii_gcd
#print axioms FourCorner.IntegralModel.primitivePairHalfSum_factorization
#print axioms FourCorner.IntegralModel.primitive_pair_half_sum_support
#print axioms FourCorner.IntegralModel.primitive_radius_half_sums
