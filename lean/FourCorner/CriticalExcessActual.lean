import FourCorner.CriticalSeventeenActual

namespace FourCorner.IntegralModel

/-- The coordinate root of minus one at an arbitrary content prime. -/
def contentPrimeIota (M : IntegralModel) (p : ℕ) [Fact p.Prime] : ZMod p :=
  (M.Y : ZMod p) / (M.X : ZMod p)

/-- The normalized horizontal squared-radius difference. -/
def contentPrimeShift (M : IntegralModel) (p : ℕ) : ZMod p :=
  -2 * (M.reducedSide : ZMod p) * (M.X : ZMod p)

/-- Actual coordinate units and their isotropic norm at every content prime. -/
theorem content_prime_coordinate_data (M : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hG : p ∣ M.radiusContent) :
    (M.X : ZMod p) ≠ 0 ∧ (M.Y : ZMod p) ≠ 0 ∧
      (M.L : ZMod p) = 0 ∧ (M.X : ZMod p)^2 + (M.Y : ZMod p)^2 = 0 := by
  have hodd : p ≠ 2 := by intro he; subst p; exact M.radiusContent_odd hG
  have pg : (p : ℤ) ∣ (M.radiusContent : ℤ) := Int.natCast_dvd_natCast.mpr hG
  have h₀ := dvd_trans pg M.radiusContent_dvd₀
  have h₁ := dvd_trans pg M.radiusContent_dvd₁
  have h₂ := dvd_trans pg M.radiusContent_dvd₂
  have h₃ := dvd_trans pg M.radiusContent_dvd₃
  obtain ⟨hl, hx, hy, _⟩ := M.common_radius_prime_support hp hodd h₀ h₁ h₂ h₃
  have ha : (M.A₀ : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd M.A₀ p).mpr h₀
  refine ⟨?_, ?_, (ZMod.intCast_zmod_eq_zero_iff_dvd M.L p).mpr hl, ?_⟩
  · exact fun h => hx ((ZMod.intCast_zmod_eq_zero_iff_dvd M.X p).mp h)
  · exact fun h => hy ((ZMod.intCast_zmod_eq_zero_iff_dvd M.Y p).mp h)
  · have h := congrArg (fun z : ℤ => (z : ZMod p)) M.sq₀
    push_cast at h
    simpa [ha] using h.symm

/-- The actual coordinate ratio is a square root of minus one at a content prime. -/
theorem contentPrimeIota_sq (M : IntegralModel) {p : ℕ} [Fact p.Prime]
    (hG : p ∣ M.radiusContent) : M.contentPrimeIota p ^ 2 = -1 := by
  obtain ⟨hx, _, _, he⟩ := M.content_prime_coordinate_data Fact.out hG
  dsimp [contentPrimeIota]
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 hx)).mpr
  linear_combination he

/-- A reduced-side unit gives a nonzero normalized square step. -/
theorem contentPrimeShift_ne_zero (M : IntegralModel) {p : ℕ} [Fact p.Prime]
    (hG : p ∣ M.radiusContent) (hH : ¬ (p : ℤ) ∣ M.reducedSide) :
    M.contentPrimeShift p ≠ 0 := by
  have hp : p.Prime := Fact.out
  have hx := (M.content_prime_coordinate_data hp hG).1
  have hHu : (M.reducedSide : ZMod p) ≠ 0 := by
    intro h
    exact hH ((ZMod.intCast_zmod_eq_zero_iff_dvd M.reducedSide p).mp h)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp (by simpa using h)
    have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (Int.natCast_dvd_natCast.mp hd)
    exact M.radiusContent_odd (he ▸ hG)
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hHu) hx

/-- The complete actual square pattern at any critical content prime. -/
theorem content_prime_square_pattern (M : IntegralModel) {p : ℕ} [Fact p.Prime]
    (hG : p ∣ M.radiusContent) (hH : ¬ (p : ℤ) ∣ M.reducedSide) :
    M.contentPrimeIota p ^ 2 = -1 ∧ M.contentPrimeShift p ≠ 0 ∧
    (M.criticalReducedRadius 1 : ZMod p)^2 =
      (M.criticalReducedRadius 0 : ZMod p)^2 + M.contentPrimeShift p ∧
    (M.criticalReducedRadius 2 : ZMod p)^2 =
      (M.criticalReducedRadius 0 : ZMod p)^2 + M.contentPrimeIota p * M.contentPrimeShift p ∧
    (M.criticalReducedRadius 3 : ZMod p)^2 =
      (M.criticalReducedRadius 0 : ZMod p)^2 + (1 + M.contentPrimeIota p) * M.contentPrimeShift p := by
  obtain ⟨hx, _, hl, _⟩ := M.content_prime_coordinate_data Fact.out hG
  have h₁ := congrArg (fun z : ℤ => (z : ZMod p)) (M.criticalReducedRadius_sq_sub 0 1)
  have h₂ := congrArg (fun z : ℤ => (z : ZMod p)) (M.criticalReducedRadius_sq_sub 0 2)
  have h₃ := congrArg (fun z : ℤ => (z : ZMod p)) (M.criticalReducedRadius_sq_sub 0 3)
  simp [pairDifferenceFactor] at h₁ h₂ h₃
  rw [hl] at h₁ h₂ h₃
  refine ⟨M.contentPrimeIota_sq hG, M.contentPrimeShift_ne_zero hG hH, ?_, ?_, ?_⟩
  · dsimp [contentPrimeShift]
    linear_combination h₁
  · dsimp [contentPrimeIota, contentPrimeShift]
    field_simp [hx]
    linear_combination h₂
  · dsimp [contentPrimeIota, contentPrimeShift]
    field_simp [hx]
    linear_combination h₃

/-- Excess over the common-content valuation means an actual reduced radius vanishes. -/
theorem excess_dvd_reducedRadius (M : IntegralModel) {p : ℕ} (hp : p.Prime)
    (i : Fin 4)
    (h : padicValNat p M.radiusContent < padicValInt p (M.pairRadius i)) :
    (p : ℤ) ∣ M.criticalReducedRadius i := by
  let : Fact p.Prime := ⟨hp⟩
  have hG : (M.radiusContent : ℤ) ≠ 0 := by exact_mod_cast M.radiusContent_pos.ne'
  have hfac : (M.radiusContent : ℤ) * M.criticalReducedRadius i = M.pairRadius i :=
    Int.mul_ediv_cancel' (M.radiusContent_dvd_pairRadius i)
  have ha : M.criticalReducedRadius i ≠ 0 := by
    intro he
    rw [he, mul_zero] at hfac
    exact (M.pairRadius_pos i).ne' hfac.symm
  by_contra hd
  have hv := congrArg (padicValInt p) hfac
  rw [padicValInt.mul hG ha, padicValInt.eq_zero_of_not_dvd hd, add_zero] at hv
  have hgval : padicValInt p (M.radiusContent : ℤ) = padicValNat p M.radiusContent := by
    simp only [padicValInt, Int.natAbs_natCast]
  rw [hgval] at hv
  omega

/-- A radius with excess valuation forces the reduced side to be a prime unit. -/
theorem excess_not_dvd_reducedSide (M : IntegralModel) {p : ℕ} (hp : p.Prime)
    (i : Fin 4)
    (h : padicValNat p M.radiusContent < padicValInt p (M.pairRadius i)) :
    ¬ (p : ℤ) ∣ M.reducedSide := by
  intro hH
  have hd := M.excess_dvd_reducedRadius hp i h
  have hu := M.normalized_radii_units hp hH
  fin_cases i
  · exact hu.1 hd
  · exact hu.2.1 hd
  · exact hu.2.2.1 hd
  · exact hu.2.2.2 hd

/-- Every excess-radius prime has exactly critical side valuation. -/
theorem excess_critical_valuation (M : IntegralModel) {p : ℕ} (hp : p.Prime)
    (i : Fin 4)
    (h : padicValNat p M.radiusContent < padicValInt p (M.pairRadius i)) :
    padicValInt p M.L = 2 * padicValNat p M.radiusContent := by
  let : Fact p.Prime := ⟨hp⟩
  have hH := M.excess_not_dvd_reducedSide hp i h
  have hG : (M.radiusContent : ℤ) ≠ 0 := by exact_mod_cast M.radiusContent_pos.ne'
  rw [← M.reducedSide_factorization,
    padicValInt.mul (pow_ne_zero 2 hG) M.reducedSide_pos.ne',
    padicValInt.eq_zero_of_not_dvd hH, add_zero]
  simp only [padicValInt, Int.natAbs_pow, Int.natAbs_natCast, padicValNat.pow]

/-- The zero in the residue pattern is an actual chosen radius with excess valuation. -/
theorem excess_reducedRadius_eq_zero (M : IntegralModel) {p : ℕ} (hp : p.Prime)
    (i : Fin 4)
    (h : padicValNat p M.radiusContent < padicValInt p (M.pairRadius i)) :
    (M.criticalReducedRadius i : ZMod p) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (M.excess_dvd_reducedRadius hp i h)

/-- The actual critical square pattern, with the two field parameters exhibited. -/
theorem critical_prime_square_pattern (M : IntegralModel) {p : ℕ} (hp : p.Prime)
    (hG : p ∣ M.radiusContent)
    (hcrit : padicValInt p M.L = 2 * padicValNat p M.radiusContent) :
    ∃ i b : ZMod p, i ^ 2 = -1 ∧ b ≠ 0 ∧
      (M.criticalReducedRadius 1 : ZMod p)^2 =
        (M.criticalReducedRadius 0 : ZMod p)^2 + b ∧
      (M.criticalReducedRadius 2 : ZMod p)^2 =
        (M.criticalReducedRadius 0 : ZMod p)^2 + i * b ∧
      (M.criticalReducedRadius 3 : ZMod p)^2 =
        (M.criticalReducedRadius 0 : ZMod p)^2 + (1 + i) * b := by
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨M.contentPrimeIota p, M.contentPrimeShift p,
    M.content_prime_square_pattern hG (M.critical_prime_not_dvd_reducedSide hp hcrit)⟩

end FourCorner.IntegralModel

#print axioms FourCorner.IntegralModel.content_prime_square_pattern
#print axioms FourCorner.IntegralModel.excess_critical_valuation
