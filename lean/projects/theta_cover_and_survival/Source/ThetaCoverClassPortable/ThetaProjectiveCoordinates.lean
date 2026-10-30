import Mathlib.Tactic
namespace FourCorner.ThetaProjectiveCoordinates
variable {K : Type*} [Field K] [CharZero K]
def Source (p q r z t : K) : Prop :=
  p^2 = z^2 + 50*t^2 ∧ q^2 = z^2 + 14*z*t + 51*t^2 ∧
  r^2 = z^2 - 14*z*t + 51*t^2
def Quartic (x y z : K) : K :=
  9801*(x^4+y^4)+19598*x^2*y^2-39592*(x^2+y^2)*z^2+39984*z^4
theorem origin : Source (1:K) 1 1 1 0 ∧ Quartic (1:K) 1 1 = 0 := by
  norm_num [Source, Quartic]
theorem boundary_iff (p q r : K) :
    Source p q r 1 0 ↔
      (p = 1 ∨ p = -1) ∧ (q = 1 ∨ q = -1) ∧ (r = 1 ∨ r = -1) := by
  simp [Source, sq_eq_one_iff]
theorem source_involution {p q r z t : K} (h : Source p q r z t) :
    Source (-p) (-q) (-r) z t := by
  simpa only [Source, neg_sq] using h
theorem no_basepoint {p q r z t : K} (h : Source p q r z t)
    (hp : p = 0) (hq : q = 0) (hr : r = 0) : z = 0 ∧ t = 0 := by
  rcases h with ⟨h₁,h₂,h₃⟩
  rw [hp, zero_pow (by decide : 2 ≠ 0)] at h₁
  rw [hq, zero_pow (by decide : 2 ≠ 0)] at h₂
  rw [hr, zero_pow (by decide : 2 ≠ 0)] at h₃
  have hzT : z*t = 0 := by linear_combination (h₃-h₂)/28
  rcases mul_eq_zero.mp hzT with hz | ht
  · have ht2 : t^2 = 0 := by rw [hz] at h₁; linear_combination -h₁/50
    exact ⟨hz, (sq_eq_zero_iff).mp ht2⟩
  · have hz2 : z^2 = 0 := by rw [ht] at h₁; simpa using h₁.symm
    exact ⟨(sq_eq_zero_iff).mp hz2, ht⟩
theorem no_base_line {p q r z t : K} (h : Source p q r z t)
    (hz : z = 0) (ht : t = 0) : p = 0 ∧ q = 0 ∧ r = 0 := by
  simpa [Source, hz, ht, sq_eq_zero_iff] using h
/-- A nonzero homogeneous source vector is never proportional to its involute. -/
theorem no_projective_fixed_point {p q r z t a : K}
    (h : Source p q r z t)
    (hn : ¬ (p = 0 ∧ q = 0 ∧ r = 0 ∧ z = 0 ∧ t = 0))
    (hp : -p = a*p) (hq : -q = a*q) (hr : -r = a*r)
    (hz : z = a*z) (ht : t = a*t) : False := by
  by_cases ha : a = 1
  · subst a
    have hp0 : p = 0 := by linear_combination -hp/2
    have hq0 : q = 0 := by linear_combination -hq/2
    have hr0 : r = 0 := by linear_combination -hr/2
    obtain ⟨hz0,ht0⟩ := no_basepoint h hp0 hq0 hr0
    exact hn ⟨hp0,hq0,hr0,hz0,ht0⟩
  · have hz0 : z = 0 := by
      have : (1-a)*z = 0 := by linear_combination hz
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm ha))
    have ht0 : t = 0 := by
      have : (1-a)*t = 0 := by linear_combination ht
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm ha))
    obtain ⟨hp0,hq0,hr0⟩ := no_base_line h hz0 ht0
    exact hn ⟨hp0,hq0,hr0,hz0,ht0⟩
theorem maps_to_quartic {p q r z t : K} (h : Source p q r z t) :
    Quartic q r p = 0 := by
  rcases h with ⟨hp,hq,hr⟩
  unfold Quartic
  linear_combination
    (39984*p^2 + 39984*z^2 + 1999200*t^2 - 39592*(q^2+r^2))*hp +
    (9801*q^2 + 9801*(z^2+14*z*t+51*t^2) + 19598*r^2 -
      39592*(z^2+50*t^2))*hq +
    (9801*r^2 + 9801*(z^2-14*z*t+51*t^2) +
      19598*(z^2+14*z*t+51*t^2) -39592*(z^2+50*t^2))*hr
/-- The literal three partial derivative polynomials have no nonzero common zero.
This is a Jacobian certificate, not an assertion of scheme smoothness. -/
theorem quartic_gradient_zero {x y z : K}
    (hx : x*(39204*x^2+39196*y^2-79184*z^2)=0)
    (hy : y*(39196*x^2+39204*y^2-79184*z^2)=0)
    (hz : z*(-79184*x^2-79184*y^2+159936*z^2)=0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  by_cases hx0 : x = 0
  · subst x
    by_cases hy0 : y = 0
    · subst y
      by_cases hz0 : z = 0
      · subst z
        exact ⟨rfl,rfl,rfl⟩
      ·
        have hzL := (mul_eq_zero.mp hz).resolve_left hz0
        have he : z^2 = 0 := by
          linear_combination (1/159936)*hzL
        exact False.elim ((pow_ne_zero 2 hz0) he)
    ·
      by_cases hz0 : z = 0
      · subst z
        have hyL := (mul_eq_zero.mp hy).resolve_left hy0
        have he : y^2 = 0 := by
          linear_combination (1/39204)*hyL
        exact False.elim ((pow_ne_zero 2 hy0) he)
      ·
        have hyL := (mul_eq_zero.mp hy).resolve_left hy0
        have hzL := (mul_eq_zero.mp hz).resolve_left hz0
        have he : y^2 = 0 := by
          linear_combination (51/8)*hyL + (101/32)*hzL
        exact False.elim ((pow_ne_zero 2 hy0) he)
  ·
    by_cases hy0 : y = 0
    · subst y
      by_cases hz0 : z = 0
      · subst z
        have hxL := (mul_eq_zero.mp hx).resolve_left hx0
        have he : x^2 = 0 := by
          linear_combination (1/39204)*hxL
        exact False.elim ((pow_ne_zero 2 hx0) he)
      ·
        have hxL := (mul_eq_zero.mp hx).resolve_left hx0
        have hzL := (mul_eq_zero.mp hz).resolve_left hz0
        have he : x^2 = 0 := by
          linear_combination (51/8)*hxL + (101/32)*hzL
        exact False.elim ((pow_ne_zero 2 hx0) he)
    ·
      by_cases hz0 : z = 0
      · subst z
        have hxL := (mul_eq_zero.mp hx).resolve_left hx0
        have hyL := (mul_eq_zero.mp hy).resolve_left hy0
        have he : x^2 = 0 := by
          linear_combination (9801/156800)*hxL + (-9799/156800)*hyL
        exact False.elim ((pow_ne_zero 2 hx0) he)
      ·
        have hxL := (mul_eq_zero.mp hx).resolve_left hx0
        have hyL := (mul_eq_zero.mp hy).resolve_left hy0
        have hzL := (mul_eq_zero.mp hz).resolve_left hz0
        have he : x^2 = 0 := by
          linear_combination (-1/392)*hxL + (-25/196)*hyL + (-101/1568)*hzL
        exact False.elim ((pow_ne_zero 2 hx0) he)
#print axioms quartic_gradient_zero
#print axioms origin
#print axioms boundary_iff
#print axioms source_involution
#print axioms no_basepoint
#print axioms no_projective_fixed_point
#print axioms maps_to_quartic
end FourCorner.ThetaProjectiveCoordinates
