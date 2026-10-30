import Mathlib.Tactic

namespace FourCorner

/-- The quadratic coefficient used in the bitangent coefficient equations. -/
def thetaBitangentF {K : Type*} [Field K] (s : K) : K :=
  9801 - 39592 * s + 39984 * s ^ 2

/-- The derivative of `thetaBitangentF`. -/
def thetaBitangentG {K : Type*} [Field K] (s : K) : K :=
  -39592 + 79968 * s

/-- The mixed coefficient used in the bitangent coefficient equations. -/
def thetaBitangentH {K : Type*} [Field K] (s t : K) : K :=
  19598 - 39592 * (s + t) + 239904 * s * t

/-- The first eliminated bitangent equation. -/
def thetaBitangentI {K : Type*} [Field K] (s t : K) : K :=
  thetaBitangentG s ^ 2 * thetaBitangentF t -
    thetaBitangentG t ^ 2 * thetaBitangentF s

/-- The second eliminated bitangent equation. -/
def thetaBitangentII {K : Type*} [Field K] (s t : K) : K :=
  4 * s * t * thetaBitangentG s ^ 3 -
    4 * thetaBitangentF s * thetaBitangentG s * thetaBitangentH s t +
    8 * thetaBitangentF s ^ 2 * thetaBitangentG t

variable {K : Type*} [Field K]

theorem thetaBitangentI_factor (s t : K) :
    thetaBitangentI s t = 2458624 * (s - t) * (102 * s + 102 * t - 101) := by
  unfold thetaBitangentI thetaBitangentF thetaBitangentG
  ring

theorem thetaBitangentII_diagonal_factor (s : K) :
    thetaBitangentII s s =
      6272 * (196 * s - 121) * (196 * s - 81) * (204 * s - 101) := by
  unfold thetaBitangentII thetaBitangentF thetaBitangentG thetaBitangentH
  ring

variable [CharZero K]

theorem thetaBitangentII_antidiagonal_factor (s : K) :
    17 * thetaBitangentII s (101 / 102 - s) =
      307328 * (68 * s - 27) * (204 * s - 121) * (204 * s - 101) := by
  unfold thetaBitangentII thetaBitangentF thetaBitangentG thetaBitangentH
  norm_num
  ring

/-- The two eliminated equations give the four bitangent ratios when the
    derivative coefficient is nonzero. -/
theorem thetaBitangent_equations_four_cases {s t : K}
    (hI : thetaBitangentI s t = 0)
    (hII : thetaBitangentII s t = 0)
    (hg : thetaBitangentG s ≠ 0) :
    (s = 81 / 196 ∧ t = 81 / 196) ∨
    (s = 121 / 196 ∧ t = 121 / 196) ∨
    (s = 27 / 68 ∧ t = 121 / 204) ∨
    (s = 121 / 204 ∧ t = 27 / 68) := by
  have hgnz : 204 * s - 101 ≠ 0 := by
    intro hz
    apply hg
    unfold thetaBitangentG
    linear_combination 392 * hz
  have hsplit : (s - t) * (102 * s + 102 * t - 101) = 0 := by
    rw [thetaBitangentI_factor] at hI
    have hconst : (2458624 : K) ≠ 0 := by norm_num
    apply (mul_eq_zero.mp ?_).resolve_left hconst
    linear_combination hI
  rcases mul_eq_zero.mp hsplit with hdiag | hsum
  · have ht : t = s := (sub_eq_zero.mp hdiag).symm
    subst t
    have hprod : (196 * s - 121) * (196 * s - 81) * (204 * s - 101) = 0 := by
      rw [thetaBitangentII_diagonal_factor] at hII
      have hconst : (6272 : K) ≠ 0 := by norm_num
      apply (mul_eq_zero.mp ?_).resolve_left hconst
      linear_combination hII
    have htwo := (mul_eq_zero.mp hprod).resolve_right hgnz
    rcases mul_eq_zero.mp htwo with h121 | h81
    · have hs : s = 121 / 196 := by linear_combination (1 / 196 : K) * h121
      exact Or.inr (Or.inl ⟨hs, hs⟩)
    · have hs : s = 81 / 196 := by linear_combination (1 / 196 : K) * h81
      exact Or.inl ⟨hs, hs⟩
  · have ht : t = 101 / 102 - s := by linear_combination (1 / 102 : K) * hsum
    have hprod : (68 * s - 27) * (204 * s - 121) * (204 * s - 101) = 0 := by
      rw [ht] at hII
      have hfac := thetaBitangentII_antidiagonal_factor s
      have hconst : (307328 : K) ≠ 0 := by norm_num
      apply (mul_eq_zero.mp ?_).resolve_left hconst
      linear_combination 17 * hII - hfac
    have htwo := (mul_eq_zero.mp hprod).resolve_right hgnz
    rcases mul_eq_zero.mp htwo with h27 | h121
    · have hs : s = 27 / 68 := by linear_combination (1 / 68 : K) * h27
      have ht' : t = 121 / 204 := by rw [ht, hs]; norm_num
      exact Or.inr (Or.inr (Or.inl ⟨hs, ht'⟩))
    · have hs : s = 121 / 204 := by linear_combination (1 / 204 : K) * h121
      have ht' : t = 27 / 68 := by rw [ht, hs]; norm_num
      exact Or.inr (Or.inr (Or.inr ⟨hs, ht'⟩))

/-- The raw coefficient-equation form of the four-case classification. -/
theorem theta_bitangent_cases {s t : K}
    (hg : thetaBitangentG s ≠ 0)
    (hI : thetaBitangentG s ^ 2 * thetaBitangentF t -
      thetaBitangentG t ^ 2 * thetaBitangentF s = 0)
    (hII : 4 * s * t * thetaBitangentG s ^ 3 -
      4 * thetaBitangentF s * thetaBitangentG s * thetaBitangentH s t +
      8 * thetaBitangentF s ^ 2 * thetaBitangentG t = 0) :
    (s = 81 / 196 ∧ t = 81 / 196) ∨
    (s = 121 / 196 ∧ t = 121 / 196) ∨
    (s = 27 / 68 ∧ t = 121 / 204) ∨
    (s = 121 / 204 ∧ t = 27 / 68) :=
  thetaBitangent_equations_four_cases hI hII hg

#print axioms theta_bitangent_cases

end FourCorner
