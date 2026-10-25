import FourCorner.ThetaLocalOdd
import FourCorner.ThetaLocalReal
import FourCorner.ThetaLocalThree
import FourCorner.ThetaLocalTwo
import FourCorner.ThetaLocalTwoSuff

namespace FourCorner

/-- The norm of the rational parameter at every prime dividing its base. -/
theorem theta_parameter_norm_gt_one {p : ℕ} [Fact p.Prime]
    {M : ℕ} (hM : M ≠ 0) (hpM : p ∣ M) (k : ℕ) :
    1 < ‖(thetaLocalParameter M k : ℚ_[p])‖ := by
  have hM0 : (M : ℚ_[p]) ≠ 0 := by exact_mod_cast hM
  have hn : ‖(M : ℚ_[p])‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hpM
  have hn0 : 0 < ‖(M : ℚ_[p])‖ := norm_pos_iff.mpr hM0
  have hpow : ‖(M : ℚ_[p])‖^(k+1) < 1 := pow_lt_one₀ (le_of_lt hn0) hn (by omega)
  have hpow0 : 0 < ‖(M : ℚ_[p])‖^(k+1) := pow_pos hn0 _
  simp only [thetaLocalParameter, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast,
    norm_div, norm_one, norm_pow]
  exact (lt_div_iff₀ hpow0).mpr (by simpa using hpow)

/-- The prescribed common denominator base is at least six. -/
theorem theta_finite_base_ge_six (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    6 ≤ 6 * ∏ p ∈ S, p := by
  have hp : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hS p hp).pos)
  omega

/-- Every prime in the finite set divides the one common denominator base. -/
theorem theta_prime_dvd_finite_base (S : Finset ℕ) {p : ℕ} (hp : p ∈ S) :
    p ∣ 6 * ∏ q ∈ S, q :=
  dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp) 6

/-- Simultaneous roots in Q2 are exactly the negative-valuation coordinates. -/
theorem theta_two_source_iff_negative_valuation (z : ℚ_[2]) :
    ThetaLocalSource 2 z ↔ z.valuation < 0 := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR⟩
    exact (theta_padic_norm_gt_one_iff_negative_valuation z).mp
      (theta_q2_first_square_norm_gt_one hP)
  · intro hz
    exact theta_two_source_of_norm_gt_one z
      ((theta_padic_norm_gt_one_iff_negative_valuation z).mpr hz)

/-- Simultaneous roots in Q3 are exactly the negative-valuation coordinates. -/
theorem theta_three_source_iff_negative_valuation (z : ℚ_[3]) :
    ThetaLocalSource 3 z ↔ z.valuation < 0 := by
  constructor
  · rintro ⟨P, Q, R, hP, hQ, hR⟩
    exact theta3_valuation_neg_of_roots z P Q R hP hQ hR
  · intro hz
    exact theta_odd_local_source (by decide) z
      ((theta_padic_norm_gt_one_iff_negative_valuation z).mpr hz)

/-- Uniform sufficiency for every prime, including two. -/
theorem theta_all_prime_local_source {p : ℕ} [Fact p.Prime]
    (z : ℚ_[p]) (hz : 1 < ‖z‖) : ThetaLocalSource p z := by
  by_cases hp : p=2
  · subst p
    exact theta_two_source_of_norm_gt_one z hz
  · exact theta_odd_local_source hp z hz

/-- One rational parameter has simultaneous roots at each prime dividing M. -/
theorem theta_parameter_local_source {p : ℕ} [Fact p.Prime]
    {M : ℕ} (hM : M ≠ 0) (hpM : p ∣ M) (k : ℕ) :
    ThetaLocalSource p (thetaLocalParameter M k : ℚ_[p]) :=
  theta_all_prime_local_source _ (theta_parameter_norm_gt_one hM hpM k)

/-- Local solubility uses the actual completion at the specified prime. -/
def ThetaLocallySolubleAt (p : ℕ) (hp : Nat.Prime p) (z : ℚ) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ThetaLocalSource p (z : ℚ_[p])

/-- The explicit common-base family simultaneously satisfies an arbitrary
finite set of local square conditions and the strict real metric conditions. -/
theorem theta_finite_prime_family (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (k : ℕ) :
    (∀ (p : ℕ) (hp : p ∈ S),
      ThetaLocallySolubleAt p (hS p hp) (thetaLocalParameter (6*∏ q ∈ S, q) k)) ∧
    (∃ P Q R : ℝ,
      RealThetaPositiveSource P Q R (thetaLocalParameter (6*∏ q ∈ S, q) k : ℝ)) := by
  have hM := theta_finite_base_ge_six S hS
  constructor
  · intro p hp
    let : Fact p.Prime := ⟨hS p hp⟩
    exact theta_parameter_local_source (by omega) (theta_prime_dvd_finite_base S hp) k
  · obtain ⟨P, Q, R, hs, _⟩ := theta_local_parameter_real_sources hM k
    exact ⟨P, Q, R, hs⟩

/-- Full finite-set assertion of Proposition theta-finite-primes: infinitely
many rational z have simultaneous local roots at all prescribed primes, with
positive real roots lying in the literal strict source U. -/
theorem theta_finite_prime_sieve (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Set.Infinite {z : ℚ |
      (∀ (p : ℕ) (hp : p ∈ S), ThetaLocallySolubleAt p (hS p hp) z) ∧
      ∃ P Q R : ℝ, RealThetaPositiveSource P Q R (z : ℝ)} := by
  have hM := theta_finite_base_ge_six S hS
  apply (theta_local_parameter_infinite hM).mono
  rintro z ⟨k, rfl⟩
  exact theta_finite_prime_family S hS k

/-- Proposition theta-finite-primes, all three assertions in one statement. -/
theorem theta_finite_primes :
    (∀ z : ℚ_[2], ThetaLocalSource 2 z ↔ z.valuation < 0) ∧
    (∀ z : ℚ_[3], ThetaLocalSource 3 z ↔ z.valuation < 0) ∧
    (∀ (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p),
      Set.Infinite {z : ℚ |
        (∀ (p : ℕ) (hp : p ∈ S), ThetaLocallySolubleAt p (hS p hp) z) ∧
        ∃ P Q R : ℝ, RealThetaPositiveSource P Q R (z : ℝ)}) :=
  ⟨theta_two_source_iff_negative_valuation, theta_three_source_iff_negative_valuation,
    theta_finite_prime_sieve⟩

#print axioms theta_finite_primes
#print axioms theta_two_source_iff_negative_valuation
#print axioms theta_three_source_iff_negative_valuation
#print axioms theta_all_prime_local_source
#print axioms theta_parameter_local_source
#print axioms theta_finite_prime_family
#print axioms theta_finite_prime_sieve
#print axioms theta_parameter_norm_gt_one
#print axioms theta_finite_base_ge_six
#print axioms theta_prime_dvd_finite_base
end FourCorner
