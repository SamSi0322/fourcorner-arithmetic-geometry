import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-! Field-independent torsion translation, for finite reduction and local fields. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourCorner.CommonSource.OverField

variable {K : Type*} [Field K] [DecidableEq K]

def curve (n : K) : WeierstrassCurve K := ⟨0, 0, 0, -(n^2), 0⟩
abbrev Point (n : K) := (curve n).toAffine.Point

omit [DecidableEq K] in
theorem nonsingular_zero (n : K) (hn : n ≠ 0) : (curve n).toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_zero]
  simp [curve, WeierstrassCurve.toAffine, hn]

def T0 (n : K) (hn : n ≠ 0) : Point n := .some 0 0 (nonsingular_zero n hn)

def coordinates {n : K} : Point n → Option (K × K)
  | .zero => none
  | .some x y _ => some (x,y)

omit [DecidableEq K] in
@[simp] theorem coordinates_T0 (n : K) (hn : n ≠ 0) :
    coordinates (T0 n hn) = some (0,0) := rfl

omit [DecidableEq K] in
theorem coordinates_injective {n : K} : Function.Injective (coordinates (n := n)) := by
  intro P Q h
  cases P <;> cases Q <;> simp_all [coordinates]

omit [DecidableEq K] in
@[simp] theorem T0_ne_zero (n : K) (hn : n ≠ 0) : T0 n hn ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

@[simp] theorem T0_add_self (n : K) (hn : n ≠ 0) : T0 n hn + T0 n hn = 0 := by
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY, curve, WeierstrassCurve.toAffine]

omit [DecidableEq K] in
theorem cubic_equation {n x y : K} (h : (curve n).toAffine.Nonsingular x y) :
    y ^ 2 = x * (x-n) * (x+n) := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [curve, WeierstrassCurve.toAffine, zero_mul, add_zero] at heq
  linear_combination heq

/-- Both coordinates of addition by the nonzero point `(0,0)` in any field. -/
theorem coordinates_add_T0 {n x y : K} (hn : n ≠ 0)
    (h : (curve n).toAffine.Nonsingular x y) (hx : x ≠ 0) :
    coordinates ((.some x y h : Point n) + T0 n hn) =
      some (-n^2 / x, n^2*y/x^2) := by
  have hc := cubic_equation h
  unfold T0
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  simp only [coordinates, WeierstrassCurve.Affine.slope_of_X_ne hx,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    curve, WeierstrassCurve.toAffine, sub_zero, zero_mul, add_zero]
  congr 1
  apply Prod.ext
  · dsimp
    field_simp
    linear_combination hc
  · dsimp
    field_simp
    linear_combination -y * hc

/-- The group-theoretic part of the cyclic odd-prime case, independent of coordinates. -/
theorem add_T0_eq_neg_of_double {n : K} (hn : n ≠ 0) {A : Point n}
    (hA : 2 • A = T0 n hn) : A + T0 n hn = -A := by
  have hfour : (A + T0 n hn) + A = 0 := by
    calc
      (A + T0 n hn) + A = (A+A) + T0 n hn := by abel
      _ = T0 n hn + T0 n hn := by rw [← two_nsmul, hA]
      _ = 0 := T0_add_self n hn
  exact eq_neg_of_add_eq_zero_left hfour

theorem addOrderOf_eq_four_of_double {n : K} (hn : n ≠ 0) {A : Point n}
    (hA : 2 • A = T0 n hn) : addOrderOf A = 4 := by
  have htwo : 2 • A ≠ 0 := by rw [hA]; exact T0_ne_zero n hn
  have hfour : 4 • A = 0 := by
    calc
      4 • A = 2 • (2 • A) := by simp [smul_smul]
      _ = 2 • T0 n hn := by rw [hA]
      _ = 0 := by rw [two_nsmul, T0_add_self]
  exact addOrderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using htwo)
    (by simpa using hfour)

/-- A half of `T0` has `x/n` a square root of `-1`, as used in §6. -/
theorem normalized_x_square_of_double {n x y : K} (hn : n ≠ 0)
    (h : (curve n).toAffine.Nonsingular x y)
    (hA : 2 • (.some x y h : Point n) = T0 n hn) : (x/n)^2 = -1 := by
  have hx : x ≠ 0 := by
    intro hx
    have hy : y = 0 := by
      have hc := cubic_equation h
      rw [hx] at hc
      simpa using hc
    have hp : (.some x y h : Point n) = T0 n hn := by
      apply coordinates_injective
      simp [coordinates, T0, hx, hy]
    rw [hp, two_nsmul, T0_add_self] at hA
    exact T0_ne_zero n hn hA.symm
  have heq := congrArg coordinates (add_T0_eq_neg_of_double hn hA)
  rw [coordinates_add_T0 hn h hx] at heq
  simp only [WeierstrassCurve.Affine.Point.neg_some, coordinates,
    Option.some.injEq, Prod.mk.injEq] at heq
  have heqx : -n^2 / x = x := heq.1
  have hsq : x^2 = -n^2 := by
    have hh := (div_eq_iff hx).mp heqx
    simpa [pow_two] using hh.symm
  rw [div_pow, hsq]
  field_simp

#print axioms coordinates_add_T0
#print axioms normalized_x_square_of_double
#print axioms addOrderOf_eq_four_of_double

end FourCorner.CommonSource.OverField
