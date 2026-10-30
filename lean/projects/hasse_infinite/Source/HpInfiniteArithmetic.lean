import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace FourCorner.HpInfiniteArithmetic

def N (j : ℕ) : ℚ := 3 + 154 * j
def M (j : ℕ) : ℚ := N j + 2
def D (j : ℕ) : ℚ := N j ^ 2 + 2 * M j ^ 2
def r (j : ℕ) : ℚ := 8 * M j * N j / D j
def s (j : ℕ) : ℚ := 2 * (N j ^ 2 - 2 * M j ^ 2) / D j
def p (j : ℕ) : ℚ := 3 - s j ^ 2

theorem N_ge (j : ℕ) : 3 ≤ N j := by
  unfold N
  have : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
  linarith
theorem D_pos (j : ℕ) : 0 < D j := by
  have h := N_ge j
  unfold D M
  positivity

theorem conic (j : ℕ) : r j ^ 2 + 2 * s j ^ 2 = 8 := by
  have hd := ne_of_gt (D_pos j)
  unfold r s
  field_simp
  unfold D
  ring

theorem r_square (j : ℕ) : r j ^ 2 = 2 * (p j + 1) := by
  have := conic j
  unfold p
  linarith

/-- The displayed actual rational point [s:2(p-1):2r:r] of D_U. -/
theorem rational_anchor_equations (j : ℕ) :
    (2 * (p j - 1)) ^ 2 = 2 * r j ^ 2 - 4 * p j * s j ^ 2 ∧
    (p j - 1) * (2 * r j) ^ 2 =
      2 * (p j + 1) * (r j ^ 2 - 2 * s j ^ 2) := by
  have hs : s j ^ 2 = 3 - p j := by unfold p; ring
  constructor <;> simp only [mul_pow] <;> rw [r_square, hs] <;> ring

theorem anchor_nonzero (j : ℕ) : r j ≠ 0 := by
  unfold r
  have hn := N_ge j
  have hm : 0 < M j := by unfold M; linarith
  exact ne_of_gt (div_pos (by positivity) (D_pos j))

theorem s_negative (j : ℕ) : s j < 0 := by
  have hn := N_ge j
  have hd := D_pos j
  unfold s M
  apply div_neg_of_neg_of_pos _ hd
  nlinarith [sq_nonneg (N j)]

theorem p_gt_one (j : ℕ) : 1 < p j := by
  have hn := N_ge j
  have hd := D_pos j
  have hpoly : 0 < 2 * D j ^ 2 - (2 * (N j ^ 2 - 2 * M j ^ 2)) ^ 2 := by
    unfold D M
    have h : 0 ≤ N j - 3 := by linarith
    nlinarith [sq_nonneg (N j), sq_nonneg (N j ^ 2),
      mul_nonneg h (sq_nonneg (N j)), sq_nonneg (N j - 3)]
  unfold p s
  rw [div_pow]
  have hsq : (2 * (N j ^ 2 - 2 * M j ^ 2)) ^ 2 / D j ^ 2 < 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hd)).2 (by linarith)
  linarith

theorem s_strictMono : StrictMono s := by
  intro i j hij
  have hi := N_ge i
  have hj := N_ge j
  have hn : N i < N j := by
    unfold N
    have hc : (i : ℚ) < (j : ℚ) := by exact_mod_cast hij
    linarith
  have hid := D_pos i
  have hjd := D_pos j
  unfold s
  apply (div_lt_div_iff₀ hid hjd).2
  have factor :
      2 * (N j ^ 2 - 2 * M j ^ 2) * D i -
        2 * (N i ^ 2 - 2 * M i ^ 2) * D j =
      32 * (N j - N i) * (N i * N j + N i + N j) := by
    unfold D M
    ring
  have hp : 0 < 32 * (N j - N i) * (N i * N j + N i + N j) := by
    positivity
  linarith

theorem p_strictMono : StrictMono p := by
  intro i j hij
  have hs := s_strictMono hij
  have hi := s_negative i
  have hj := s_negative j
  unfold p
  nlinarith

theorem parameters_injective : Function.Injective p := p_strictMono.injective

theorem infinitely_many_parameters : Set.Infinite (Set.range p) :=
  Set.infinite_range_of_injective parameters_injective

theorem first_parameter : p 0 = 3719 / 3481 := by
  norm_num [p, s, D, M, N]

#print axioms rational_anchor_equations
#print axioms infinitely_many_parameters
#print axioms conic
#print axioms p_gt_one
#print axioms parameters_injective
#print axioms first_parameter
end FourCorner.HpInfiniteArithmetic
