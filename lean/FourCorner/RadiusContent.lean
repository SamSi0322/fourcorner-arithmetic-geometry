import FourCorner.RadiusContentPrime
import FourCorner.RadiusContentNormalize
import FourCorner.PrimitiveCongruences
import Mathlib.Data.Nat.Prime.Basic

namespace FourCorner
namespace IntegralModel

/-- Every odd common radius divisor has its full square in the denominator.
The proof uses coprimality of the second factor in the exact squared difference,
so no bounded valuation computation is involved. -/
theorem common_radius_square_dvd_L (M : IntegralModel) {G : ℕ}
    (hodd : ¬ 2 ∣ G)
    (h₀ : (G : ℤ) ∣ M.A₀) (h₁ : (G : ℤ) ∣ M.A₁)
    (h₂ : (G : ℤ) ∣ M.A₂) (h₃ : (G : ℤ) ∣ M.A₃) :
    (G : ℤ)^2 ∣ M.L := by
  have hc : Nat.Coprime G (M.L - 2 * M.X).natAbs := by
    apply Nat.coprime_of_dvd
    intro p hp hpg hpf
    have hoddp : p ≠ 2 := by intro he; subst p; exact hodd hpg
    have pg : (p : ℤ) ∣ (G : ℤ) := Int.natCast_dvd_natCast.mpr hpg
    have pa₀ := dvd_trans pg h₀
    have pa₁ := dvd_trans pg h₁
    have pa₂ := dvd_trans pg h₂
    have pa₃ := dvd_trans pg h₃
    have pl := M.common_radius_prime_dvd_L hp hoddp pa₀ pa₁ pa₂ pa₃
    have px := M.common_radius_prime_not_dvd_X hp hoddp pa₀ pa₁ pa₂ pa₃
    have pf : (p : ℤ) ∣ M.L - 2 * M.X := Int.natCast_dvd.mpr hpf
    have ptx : (p : ℤ) ∣ 2 * M.X := by
      have hh := dvd_sub pl pf
      simpa using hh
    have hn : p ∣ 2 * M.X.natAbs := by
      simpa [Int.natAbs_mul] using (Int.natCast_dvd.mp ptx)
    rcases hp.dvd_mul.mp hn with hp2 | hpX
    · exact hoddp ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2)
    · exact px (Int.natCast_dvd.mpr hpX)
  have hsq₀ := pow_dvd_pow_of_dvd h₀ 2
  have hsq₁ := pow_dvd_pow_of_dvd h₁ 2
  have hprod : (G : ℤ)^2 ∣ M.L * (M.L - 2 * M.X) := by
    have hh := dvd_sub hsq₁ hsq₀
    have he : M.A₁^2 - M.A₀^2 = M.L * (M.L - 2 * M.X) := by
      rw [M.sq₁, M.sq₀]
      ring
    rwa [he] at hh
  have hprodNat : G^2 ∣ M.L.natAbs * (M.L - 2 * M.X).natAbs := by
    have hh := Int.natAbs_dvd_natAbs.mpr hprod
    simpa [Int.natAbs_pow, Int.natAbs_mul] using hh
  have hn : G^2 ∣ M.L.natAbs := (hc.pow_left 2).dvd_of_dvd_mul_right hprodNat
  have hh : ((G^2 : ℕ) : ℤ) ∣ M.L := Int.natCast_dvd.mpr hn
  simpa using hh

/-- The common integer content of the four actual positive radii. -/
def radiusContent (M : IntegralModel) : ℕ := gcd4 M.A₀ M.A₁ M.A₂ M.A₃

/-- The denominator remaining after the square of the radius content is removed. -/
def reducedSide (M : IntegralModel) : ℤ := M.L / (M.radiusContent : ℤ)^2

theorem radiusContent_pos (M : IntegralModel) : 0 < M.radiusContent :=
  gcd4_pos _ _ _ _ M.A₀_pos

theorem radiusContent_dvd₀ (M : IntegralModel) : (M.radiusContent : ℤ) ∣ M.A₀ :=
  gcd4_dvd₀ _ _ _ _
theorem radiusContent_dvd₁ (M : IntegralModel) : (M.radiusContent : ℤ) ∣ M.A₁ :=
  gcd4_dvd₁ _ _ _ _
theorem radiusContent_dvd₂ (M : IntegralModel) : (M.radiusContent : ℤ) ∣ M.A₂ :=
  gcd4_dvd₂ _ _ _ _
theorem radiusContent_dvd₃ (M : IntegralModel) : (M.radiusContent : ℤ) ∣ M.A₃ :=
  gcd4_dvd₃ _ _ _ _

theorem radiusContent_odd (M : IntegralModel) : ¬ 2 ∣ M.radiusContent := by
  intro hg
  have ha := dvd_trans (Int.natCast_dvd_natCast.mpr hg) M.radiusContent_dvd₀
  have he := Int.emod_eq_zero_of_dvd ha
  have hodd := M.four_divides_L_and_orientation.2.2.1
  norm_num at he
  omega

theorem radiusContent_prime_mod_four (M : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hg : p ∣ M.radiusContent) : p % 4 = 1 := by
  have hodd : p ≠ 2 := by intro he; subst p; exact M.radiusContent_odd hg
  have pg : (p : ℤ) ∣ (M.radiusContent : ℤ) := Int.natCast_dvd_natCast.mpr hg
  exact M.common_radius_prime_mod_four hp hodd
    (dvd_trans pg M.radiusContent_dvd₀) (dvd_trans pg M.radiusContent_dvd₁)
    (dvd_trans pg M.radiusContent_dvd₂) (dvd_trans pg M.radiusContent_dvd₃)

/-- The square divisibility assertion in Proposition int:content. -/
theorem radiusContent_sq_dvd_L (M : IntegralModel) :
    (M.radiusContent : ℤ)^2 ∣ M.L :=
  M.common_radius_square_dvd_L M.radiusContent_odd M.radiusContent_dvd₀
    M.radiusContent_dvd₁ M.radiusContent_dvd₂ M.radiusContent_dvd₃

theorem radiusContent_coprime_six (M : IntegralModel) : M.radiusContent.Coprime 6 := by
  apply Nat.coprime_of_dvd
  intro p hp hg h6
  have hc := M.radiusContent_prime_mod_four hp hg
  have h : p = 2 ∨ p = 3 := by
    have hh : p ∣ 2 * 3 := h6
    rcases hp.dvd_mul.mp hh with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  rcases h with rfl | rfl <;> norm_num at hc

theorem radiusContent_coprime_twentyfour (M : IntegralModel) :
    M.radiusContent.Coprime 24 := by
  apply Nat.coprime_of_dvd
  intro p hp hg h24
  have hc := M.radiusContent_prime_mod_four hp hg
  have h : p = 2 ∨ p = 3 := by
    have hh : p ∣ 2^3 * 3 := h24
    rcases hp.dvd_mul.mp hh with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h2))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  rcases h with rfl | rfl <;> norm_num at hc

theorem reducedSide_factorization (M : IntegralModel) :
    (M.radiusContent : ℤ)^2 * M.reducedSide = M.L :=
  Int.mul_ediv_cancel' M.radiusContent_sq_dvd_L

theorem reducedSide_pos (M : IntegralModel) : 0 < M.reducedSide :=
  Int.ediv_pos_of_pos_of_dvd M.L_pos (sq_nonneg _) M.radiusContent_sq_dvd_L

theorem normalized_radii_primitive (M : IntegralModel) :
    gcd4 (M.A₀ / (M.radiusContent : ℤ)) (M.A₁ / (M.radiusContent : ℤ))
      (M.A₂ / (M.radiusContent : ℤ)) (M.A₃ / (M.radiusContent : ℤ)) = 1 :=
  gcd4_ediv_self _ _ _ _ (ne_of_gt M.radiusContent_pos)

/-- The content normalization retains the literal rational radius. -/
theorem normalized_radius_ratio (M : IntegralModel) {A : ℤ}
    (hA : (M.radiusContent : ℤ) ∣ A) :
    (A : ℚ) / (M.L : ℚ) =
      ((A / (M.radiusContent : ℤ) : ℤ) : ℚ) /
        ((M.radiusContent : ℚ) * (M.reducedSide : ℚ)) := by
  have hG : (M.radiusContent : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt M.radiusContent_pos)
  have hH : (M.reducedSide : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt M.reducedSide_pos)
  have hL : (M.L : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt M.L_pos)
  have hAa : (M.radiusContent : ℚ) * ((A / (M.radiusContent : ℤ) : ℤ) : ℚ) = A := by
    exact_mod_cast (Int.mul_ediv_cancel' hA)
  have hLl : (M.radiusContent : ℚ)^2 * (M.reducedSide : ℚ) = M.L := by
    exact_mod_cast M.reducedSide_factorization
  apply (div_eq_div_iff hL (mul_ne_zero hG hH)).mpr
  rw [← hAa, ← hLl]
  ring

/-- All four labelled radii are preserved by the common content normalization. -/
theorem normalized_radii_ratios (M : IntegralModel) :
    (M.A₀ : ℚ) / M.L = ((M.A₀ / (M.radiusContent : ℤ) : ℤ) : ℚ) /
      ((M.radiusContent : ℚ) * (M.reducedSide : ℚ)) ∧
    (M.A₁ : ℚ) / M.L = ((M.A₁ / (M.radiusContent : ℤ) : ℤ) : ℚ) /
      ((M.radiusContent : ℚ) * (M.reducedSide : ℚ)) ∧
    (M.A₂ : ℚ) / M.L = ((M.A₂ / (M.radiusContent : ℤ) : ℤ) : ℚ) /
      ((M.radiusContent : ℚ) * (M.reducedSide : ℚ)) ∧
    (M.A₃ : ℚ) / M.L = ((M.A₃ / (M.radiusContent : ℤ) : ℤ) : ℚ) /
      ((M.radiusContent : ℚ) * (M.reducedSide : ℚ)) :=
  ⟨M.normalized_radius_ratio M.radiusContent_dvd₀,
   M.normalized_radius_ratio M.radiusContent_dvd₁,
   M.normalized_radius_ratio M.radiusContent_dvd₂,
   M.normalized_radius_ratio M.radiusContent_dvd₃⟩

/-- The factor 24 survives removal of the content square. -/
theorem twentyfour_dvd_reducedSide (M : IntegralModel) : (24 : ℤ) ∣ M.reducedSide := by
  have hc : Nat.Coprime 24 (M.radiusContent^2) :=
    (M.radiusContent_coprime_twentyfour.pow_left 2).symm
  have hL : 24 ∣ M.L.natAbs := Int.natCast_dvd.mp M.twentyfour_dvd_L
  have hf : M.L.natAbs = M.radiusContent^2 * M.reducedSide.natAbs := by
    have hh := congrArg Int.natAbs M.reducedSide_factorization
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hh.symm
  rw [hf] at hL
  have hh := hc.dvd_of_dvd_mul_left hL
  exact Int.natCast_dvd.mpr hh

/-- Every prime dividing the reduced side misses every reduced radius. -/
theorem normalized_radii_units (M : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hpH : (p : ℤ) ∣ M.reducedSide) :
    ¬ (p : ℤ) ∣ M.A₀ / (M.radiusContent : ℤ) ∧
    ¬ (p : ℤ) ∣ M.A₁ / (M.radiusContent : ℤ) ∧
    ¬ (p : ℤ) ∣ M.A₂ / (M.radiusContent : ℤ) ∧
    ¬ (p : ℤ) ∣ M.A₃ / (M.radiusContent : ℤ) :=
  M.reduced_radii_not_dvd M.radiusContent_sq_dvd_L hp hpH

/-- The arithmetic assertions of Proposition int:content, on the actual model. -/
theorem radius_content (M : IntegralModel) :
    (M.radiusContent : ℤ)^2 ∣ M.L ∧
    (∀ p : ℕ, p.Prime → p ∣ M.radiusContent → p % 4 = 1) ∧
    Nat.gcd M.radiusContent 6 = 1 ∧
    (24 : ℤ) ∣ M.reducedSide ∧
    gcd4 (M.A₀ / (M.radiusContent : ℤ)) (M.A₁ / (M.radiusContent : ℤ))
      (M.A₂ / (M.radiusContent : ℤ)) (M.A₃ / (M.radiusContent : ℤ)) = 1 ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ M.reducedSide →
      ¬ (p : ℤ) ∣ M.A₀ / (M.radiusContent : ℤ) ∧
      ¬ (p : ℤ) ∣ M.A₁ / (M.radiusContent : ℤ) ∧
      ¬ (p : ℤ) ∣ M.A₂ / (M.radiusContent : ℤ) ∧
      ¬ (p : ℤ) ∣ M.A₃ / (M.radiusContent : ℤ)) := by
  exact ⟨M.radiusContent_sq_dvd_L, fun _ hp hg => M.radiusContent_prime_mod_four hp hg,
    M.radiusContent_coprime_six, M.twentyfour_dvd_reducedSide,
    M.normalized_radii_primitive, fun _ hp hh => M.normalized_radii_units hp hh⟩

end IntegralModel
end FourCorner
#print axioms FourCorner.IntegralModel.common_radius_square_dvd_L

#print axioms FourCorner.IntegralModel.radiusContent_prime_mod_four
#print axioms FourCorner.IntegralModel.radiusContent_sq_dvd_L
#print axioms FourCorner.IntegralModel.radiusContent_coprime_six
#print axioms FourCorner.IntegralModel.normalized_radii_primitive
#print axioms FourCorner.IntegralModel.normalized_radius_ratio
#print axioms FourCorner.IntegralModel.twentyfour_dvd_reducedSide
#print axioms FourCorner.IntegralModel.normalized_radii_units
#print axioms FourCorner.IntegralModel.radius_content

#print axioms FourCorner.IntegralModel.normalized_radii_ratios
