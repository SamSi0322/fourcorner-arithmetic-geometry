import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Exact arithmetic constituents of thm:cs-15569. No rational-group
completeness or local-source implication is asserted by this module. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace FourCorner.Cs15569Finite

abbrev F := ZMod 113
instance : Fact (Nat.Prime 113) := ⟨by norm_num⟩

def px : ℚ := 15569 * 7809 ^ 2 / 7760 ^ 2
def py : ℚ := -(15569 * 7809 * 108983 * 11009) / 7760 ^ 3
def gx : ℚ := 15569 * 13522049 ^ 2 / 13382920 ^ 2
def gy : ℚ := -(15569 * 13522049 * 1934751 * 2373852137) / 13382920 ^ 3

theorem p_on_curve : py ^ 2 = px * (px - 15569) * (px + 15569) := by
  norm_num [px, py]
theorem g_on_curve : gy ^ 2 = gx * (gx - 15569) * (gx + 15569) := by
  norm_num [gx, gy]
theorem p_factorization :
    px - 15569 = (108983 / 7760 : ℚ) ^ 2 ∧
    px + 15569 = 15569 * (11009 / 7760 : ℚ) ^ 2 := by
  norm_num [px]
theorem g_factorization :
    gx - 15569 = 15569 * (1934751 / 13382920 : ℚ) ^ 2 ∧
    gx + 15569 = (2373852137 / 13382920 : ℚ) ^ 2 := by
  norm_num [gx]

theorem n_prime : Nat.Prime 15569 := by norm_num

theorem n_local_square : (15569 : F) = 38 ^ 2 := by decide

-- These use the literal integral numerators and denominators; reduction is
-- legitimate since all four displayed denominators are nonzero at 113.
theorem denominator_units :
    (7760 : F) ≠ 0 ∧ (13382920 : F) ≠ 0 := by decide

theorem p_reduced_coordinates :
    (15569 * 7809 ^ 2 / 7760 ^ 2 : F) = 36 ∧
    (-(15569 * 7809 * 108983 * 11009) / 7760 ^ 3 : F) = 58 := by
  constructor <;> apply (div_eq_iff (by decide)).mpr <;> decide

theorem g_reduced_coordinates :
    (15569 * 13522049 ^ 2 / 13382920 ^ 2 : F) = 81 ∧
    (-(15569 * 13522049 * 1934751 * 2373852137) / 13382920 ^ 3 : F) = 112 := by
  constructor <;> apply (div_eq_iff (by decide)).mpr <;> decide

theorem residue_points_on_curve :
    ∀ xy ∈ ([(23,39), (81,112), (77,79), (0,0),
      (2,1), (7,6), (88,0), (36,58)] : List (F × F)),
      xy.2 ^ 2 = xy.1 * (xy.1 - 15569) * (xy.1 + 15569) := by
  intro xy h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> decide

-- Literal tangent-slope arithmetic, used in the paper's doubling certificate.
def doubleX (x y : F) : F := ((3 * x ^ 2 - 15569 ^ 2) / (2 * y)) ^ 2 - 2 * x
def doubleY (x y : F) : F :=
  ((3 * x ^ 2 - 15569 ^ 2) / (2 * y)) * (x - doubleX x y) - y

theorem tangent_slopes :
    ((3 * 23 ^ 2 - 15569 ^ 2) / (2 * 39) : F) = 50 ∧
    ((3 * 81 ^ 2 - 15569 ^ 2) / (2 * 112) : F) = 76 ∧
    ((3 * 77 ^ 2 - 15569 ^ 2) / (2 * 79) : F) = 70 ∧
    ((3 * 2 ^ 2 - 15569 ^ 2) / (2 * 1) : F) = 89 ∧
    ((3 * 7 ^ 2 - 15569 ^ 2) / (2 * 6) : F) = 92 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals apply (div_eq_iff (by decide)).mpr <;> decide

theorem doubling_certificate :
    (doubleX 23 39, doubleY 23 39) = (81,112) ∧
    (doubleX 81 112, doubleY 81 112) = (77,79) ∧
    (doubleX 77 79, doubleY 77 79) = (0,0) ∧
    (doubleX 2 1, doubleY 2 1) = (7,6) ∧
    (doubleX 7 6, doubleY 7 6) = (88,0) := by
  dsimp [doubleX, doubleY]
  rw [tangent_slopes.1, tangent_slopes.2.1, tangent_slopes.2.2.1,
    tangent_slopes.2.2.2.1, tangent_slopes.2.2.2.2]
  decide

def returnResidue (a c : F) : F := (a + c) / (2 * (c + 15569))

theorem return_table :
    returnResidue 11 81 = 21 ∧ returnResidue 16 87 = 71 ∧
    returnResidue 81 11 = 29 ∧ returnResidue 87 16 = 101 := by
  dsimp [returnResidue]
  constructor
  · apply (div_eq_iff (by decide)).mpr; decide
  constructor
  · apply (div_eq_iff (by decide)).mpr; decide
  constructor <;> apply (div_eq_iff (by decide)).mpr <;> decide

theorem four_returns_nonsquare :
    ∀ r ∈ ([21,71,29,101] : List F), ¬ IsSquare r := by
  have h : ∀ r ∈ ([21,71,29,101] : List F), ∀ t : F, r ≠ t * t := by decide
  intro r hr ⟨t, ht⟩
  exact h r hr t ht

/-- The final residue obstruction, quantified over every residue pair in the
exhaustive four-row image, rather than selected rational points. -/
theorem four_pair_exclusion (a c : F)
    (h : (a = 11 ∧ c = 81) ∨ (a = 16 ∧ c = 87) ∨
      (a = 81 ∧ c = 11) ∨ (a = 87 ∧ c = 16)) :
    ¬ IsSquare (returnResidue a c) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    apply four_returns_nonsquare
    simp only [return_table.1, return_table.2.1, return_table.2.2.1,
      return_table.2.2.2]
    simp

/-- Three substitutions suffice in any actual abelian group: no free basis,
rank computation, or saturation claim is needed at this algebraic step. -/
theorem mod_eight_generation {H : Type*} [AddCommGroup H] (G P : H)
    (hgen : ∀ h : H, ∃ k m : ℕ, k < 2 ∧ m < 2 ∧
      ∃ z : H, h = k • G + m • P + 2 • z) :
    ∀ h : H, ∃ k m : ℕ, k < 8 ∧ m < 8 ∧
      ∃ z : H, h = k • G + m • P + 8 • z := by
  intro h
  obtain ⟨k₀, m₀, hk₀, hm₀, z₀, hz₀⟩ := hgen h
  obtain ⟨k₁, m₁, hk₁, hm₁, z₁, hz₁⟩ := hgen z₀
  obtain ⟨k₂, m₂, hk₂, hm₂, z₂, hz₂⟩ := hgen z₁
  refine ⟨k₀ + 2 * k₁ + 4 * k₂, m₀ + 2 * m₁ + 4 * m₂,
    by omega, by omega, z₂, ?_⟩
  rw [hz₀, hz₁, hz₂]
  simp only [add_nsmul, nsmul_add]
  simp only [← mul_nsmul, Nat.mul_comm k₁ 2, Nat.mul_comm k₂ 4,
    Nat.mul_comm m₁ 2, Nat.mul_comm m₂ 4]
  have hk : k₂ * 2 * 2 = 4 * k₂ := by omega
  have hm : m₂ * 2 * 2 = 4 * m₂ := by omega
  simp only [hk, hm]
  abel

#print axioms p_on_curve
#print axioms g_on_curve
#print axioms n_prime
#print axioms doubling_certificate
#print axioms four_pair_exclusion
#print axioms mod_eight_generation
end FourCorner.Cs15569Finite
