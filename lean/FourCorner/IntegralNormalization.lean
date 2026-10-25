import FourCorner.IntegralModel
import FourCorner.RatIntegralAux
import FourCorner.PrimitiveLcmAux
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace FourCorner

/-- Dividing a primitive integral model by its positive common denominator
recovers all four labelled positive rational radii and the strict point. -/
theorem IntegralModel.toStrictPoint (P : IntegralModel) :
    StrictPoint ((P.X : ℚ) / P.L) ((P.Y : ℚ) / P.L)
      ((P.A₀ : ℚ) / P.L) ((P.A₁ : ℚ) / P.L)
      ((P.A₂ : ℚ) / P.L) ((P.A₃ : ℚ) / P.L) := by
  have hL : (0 : ℚ) < P.L := by exact_mod_cast P.L_pos
  have hLn : (P.L : ℚ) ≠ 0 := ne_of_gt hL
  refine ⟨div_pos (by exact_mod_cast P.X_pos) hL,
    (div_lt_one hL).2 (by exact_mod_cast P.X_lt),
    div_pos (by exact_mod_cast P.Y_pos) hL,
    (div_lt_one hL).2 (by exact_mod_cast P.Y_lt),
    div_pos (by exact_mod_cast P.A₀_pos) hL,
    div_pos (by exact_mod_cast P.A₁_pos) hL,
    div_pos (by exact_mod_cast P.A₂_pos) hL,
    div_pos (by exact_mod_cast P.A₃_pos) hL, ?_⟩
  have h₀ : (P.A₀ : ℚ)^2 = (P.X : ℚ)^2 + (P.Y : ℚ)^2 := by
    exact_mod_cast P.sq₀
  have h₁ : (P.A₁ : ℚ)^2 = ((P.L : ℚ)-P.X)^2 + (P.Y : ℚ)^2 := by
    exact_mod_cast P.sq₁
  have h₂ : (P.A₂ : ℚ)^2 = (P.X : ℚ)^2 + ((P.L : ℚ)-P.Y)^2 := by
    exact_mod_cast P.sq₂
  have h₃ : (P.A₃ : ℚ)^2 = ((P.L : ℚ)-P.X)^2 + ((P.L : ℚ)-P.Y)^2 := by
    exact_mod_cast P.sq₃
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
    linear_combination h₀
  · field_simp
    linear_combination h₁
  · field_simp
    linear_combination h₂
  · field_simp
    linear_combination h₃

/-- The coordinate denominator of a primitive integral model is minimal. -/
theorem IntegralModel.leastCoordinateDenominator (P : IntegralModel) :
    Nat.lcm ((P.X : ℚ) / P.L).den ((P.Y : ℚ) / P.L).den = P.L.natAbs :=
  primitive_lcm_den_ratios P.L P.X P.Y (ne_of_gt P.L_pos) P.primitive

/-- Every strict rational point has a primitive integral lift at its least
coordinate denominator. The same denominator clears all four positive radii. -/
theorem strictPoint_integralNormalization {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    ∃ P : IntegralModel,
      P.L = (Nat.lcm x.den y.den : ℤ) ∧
      (P.X : ℚ) = (P.L : ℚ) * x ∧
      (P.Y : ℚ) = (P.L : ℚ) * y ∧
      (P.A₀ : ℚ) = (P.L : ℚ) * r₀ ∧
      (P.A₁ : ℚ) = (P.L : ℚ) * r₁ ∧
      (P.A₂ : ℚ) = (P.L : ℚ) * r₂ ∧
      (P.A₃ : ℚ) = (P.L : ℚ) * r₃ := by
  rcases h with ⟨hx₀, hx₁, hy₀, hy₁, hr₀, hr₁, hr₂, hr₃, h₀, h₁, h₂, h₃⟩
  let L := Nat.lcm x.den y.den
  have hL : 0 < L := Nat.lcm_pos x.pos y.pos
  have hLQ : (0 : ℚ) < L := by exact_mod_cast hL
  obtain ⟨X, hX⟩ := (nat_mul_rat_integral_iff L x).2 (Nat.dvd_lcm_left _ _)
  obtain ⟨Y, hY⟩ := (nat_mul_rat_integral_iff L y).2 (Nat.dvd_lcm_right _ _)
  have sq₀ : ((L : ℚ) * r₀) ^ 2 = ((X ^ 2 + Y ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [← hX, ← hY]
    linear_combination (L : ℚ)^2 * h₀
  have sq₁ : ((L : ℚ) * r₁) ^ 2 = (((L : ℤ) - X)^2 + Y^2 : ℤ) := by
    push_cast
    rw [← hX, ← hY]
    linear_combination (L : ℚ)^2 * h₁
  have sq₂ : ((L : ℚ) * r₂) ^ 2 = (X^2 + ((L : ℤ) - Y)^2 : ℤ) := by
    push_cast
    rw [← hX, ← hY]
    linear_combination (L : ℚ)^2 * h₂
  have sq₃ : ((L : ℚ) * r₃) ^ 2 = (((L : ℤ) - X)^2 + ((L : ℤ) - Y)^2 : ℤ) := by
    push_cast
    rw [← hX, ← hY]
    linear_combination (L : ℚ)^2 * h₃
  obtain ⟨A₀, hA₀⟩ := exists_int_of_sq_eq_int sq₀
  obtain ⟨A₁, hA₁⟩ := exists_int_of_sq_eq_int sq₁
  obtain ⟨A₂, hA₂⟩ := exists_int_of_sq_eq_int sq₂
  obtain ⟨A₃, hA₃⟩ := exists_int_of_sq_eq_int sq₃
  rw [hA₀] at sq₀
  rw [hA₁] at sq₁
  rw [hA₂] at sq₂
  rw [hA₃] at sq₃
  have X_pos : 0 < X := by
    have : (0 : ℚ) < X := by rw [← hX]; exact mul_pos hLQ hx₀
    exact_mod_cast this
  have Y_pos : 0 < Y := by
    have : (0 : ℚ) < Y := by rw [← hY]; exact mul_pos hLQ hy₀
    exact_mod_cast this
  have X_lt : X < (L : ℤ) := by
    have : (X : ℚ) < L := by rw [← hX]; nlinarith
    exact_mod_cast this
  have Y_lt : Y < (L : ℤ) := by
    have : (Y : ℚ) < L := by rw [← hY]; nlinarith
    exact_mod_cast this
  have A₀_pos : 0 < A₀ := by
    have : (0 : ℚ) < A₀ := by rw [← hA₀]; exact mul_pos hLQ hr₀
    exact_mod_cast this
  have A₁_pos : 0 < A₁ := by
    have : (0 : ℚ) < A₁ := by rw [← hA₁]; exact mul_pos hLQ hr₁
    exact_mod_cast this
  have A₂_pos : 0 < A₂ := by
    have : (0 : ℚ) < A₂ := by rw [← hA₂]; exact mul_pos hLQ hr₂
    exact_mod_cast this
  have A₃_pos : 0 < A₃ := by
    have : (0 : ℚ) < A₃ := by rw [← hA₃]; exact mul_pos hLQ hr₃
    exact_mod_cast this
  let P : IntegralModel := {
    L := (L : ℤ), X := X, Y := Y, A₀ := A₀, A₁ := A₁, A₂ := A₂, A₃ := A₃,
    L_pos := by exact_mod_cast hL,
    X_pos := X_pos, X_lt := X_lt, Y_pos := Y_pos, Y_lt := Y_lt,
    A₀_pos := A₀_pos, A₁_pos := A₁_pos, A₂_pos := A₂_pos, A₃_pos := A₃_pos,
    primitive := by simpa using primitive_of_lcm_den x y L X Y rfl hX.symm hY.symm,
    sq₀ := by exact_mod_cast sq₀,
    sq₁ := by exact_mod_cast sq₁,
    sq₂ := by exact_mod_cast sq₂,
    sq₃ := by exact_mod_cast sq₃ }
  refine ⟨P, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hX.symm
  · exact hY.symm
  · exact hA₀.symm
  · exact hA₁.symm
  · exact hA₂.symm
  · exact hA₃.symm

/-- The original strict rational problem and primitive integral problem are
exactly equivalent, with the least coordinate denominator and all four roots. -/
theorem strictPoint_iff_primitiveIntegral {x y r₀ r₁ r₂ r₃ : ℚ} :
    StrictPoint x y r₀ r₁ r₂ r₃ ↔
    ∃ P : IntegralModel,
      P.L = (Nat.lcm x.den y.den : ℤ) ∧
      (P.X : ℚ) / P.L = x ∧ (P.Y : ℚ) / P.L = y ∧
      (P.A₀ : ℚ) / P.L = r₀ ∧ (P.A₁ : ℚ) / P.L = r₁ ∧
      (P.A₂ : ℚ) / P.L = r₂ ∧ (P.A₃ : ℚ) / P.L = r₃ := by
  constructor
  · intro h
    obtain ⟨P, hL, hX, hY, hA₀, hA₁, hA₂, hA₃⟩ :=
      strictPoint_integralNormalization h
    have hLn : (P.L : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt P.L_pos
    refine ⟨P, hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hX, mul_div_cancel_left₀ _ hLn]
    · rw [hY, mul_div_cancel_left₀ _ hLn]
    · rw [hA₀, mul_div_cancel_left₀ _ hLn]
    · rw [hA₁, mul_div_cancel_left₀ _ hLn]
    · rw [hA₂, mul_div_cancel_left₀ _ hLn]
    · rw [hA₃, mul_div_cancel_left₀ _ hLn]
  · rintro ⟨P, hL, hX, hY, hA₀, hA₁, hA₂, hA₃⟩
    rw [← hX, ← hY, ← hA₀, ← hA₁, ← hA₂, ← hA₃]
    exact P.toStrictPoint

/-- Any positive integer simultaneously clearing the two coordinates is at
least the displayed primitive denominator. -/
theorem IntegralModel.minimal_positive_clearer (P : IntegralModel)
    (N : ℕ) (hN : 0 < N)
    (hclear : ∃ X Y : ℤ,
      (N : ℚ) * ((P.X : ℚ) / P.L) = (X : ℚ) ∧
      (N : ℚ) * ((P.Y : ℚ) / P.L) = (Y : ℚ)) :
    P.L.natAbs ≤ N := by
  have hd := (pair_integral_iff_lcm_den_dvd N
    ((P.X : ℚ) / P.L) ((P.Y : ℚ) / P.L)).1 hclear
  rw [P.leastCoordinateDenominator] at hd
  exact Nat.le_of_dvd hN hd

#print axioms strictPoint_iff_primitiveIntegral
#print axioms IntegralModel.minimal_positive_clearer
#print axioms IntegralModel.toStrictPoint
#print axioms IntegralModel.leastCoordinateDenominator
#print axioms strictPoint_integralNormalization
end FourCorner
