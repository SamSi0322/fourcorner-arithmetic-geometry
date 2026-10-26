import FourCorner.OrderedSourceAlgebra
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-! Actual rational points and the torsion translations of §6. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourCorner.CommonSource

abbrev Point (n : ℚ) := (congruentCurve n).toAffine.Point

@[simp] theorem discriminant (n : ℚ) : (congruentCurve n).Δ = 64 * n ^ 6 := by
  simp [congruentCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem isElliptic {n : ℚ} (hn : n ≠ 0) : (congruentCurve n).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [discriminant]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hn))⟩

theorem nonsingular {n x y : ℚ} (hn : n ≠ 0) (h : CongruentEquation n x y) :
    (congruentCurve n).toAffine.Nonsingular x y := by
  apply (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero _).mp
    ((congruentEquation_iff_weierstrass n x y).mp h)
  change (congruentCurve n).Δ ≠ 0
  rw [discriminant]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hn)

def finitePoint {n x y : ℚ} (hn : n ≠ 0) (h : CongruentEquation n x y) : Point n :=
  .some x y (nonsingular hn h)

def O (n : ℚ) : Point n := 0

def T0 (n : ℚ) (hn : n ≠ 0) : Point n :=
  finitePoint (x := 0) (y := 0) hn (by simp [CongruentEquation])

def Tplus (n : ℚ) (hn : n ≠ 0) : Point n :=
  finitePoint (x := n) (y := 0) hn (by simp [CongruentEquation])

def Tminus (n : ℚ) (hn : n ≠ 0) : Point n :=
  finitePoint (x := -n) (y := 0) hn (by simp [CongruentEquation])

/-- Coordinates retain the distinction between infinity and `(0,0)`. -/
def coordinates {n : ℚ} : Point n → Option (ℚ × ℚ)
  | .zero => none
  | .some x y _ => some (x, y)

@[simp] theorem coordinates_finitePoint {n x y : ℚ} (hn : n ≠ 0)
    (h : CongruentEquation n x y) : coordinates (finitePoint hn h) = some (x,y) := rfl

@[simp] theorem coordinates_O (n : ℚ) : coordinates (O n) = none := rfl
@[simp] theorem coordinates_T0 (n : ℚ) (hn : n ≠ 0) : coordinates (T0 n hn) = some (0,0) := rfl
@[simp] theorem coordinates_Tplus (n : ℚ) (hn : n ≠ 0) : coordinates (Tplus n hn) = some (n,0) := rfl
@[simp] theorem coordinates_Tminus (n : ℚ) (hn : n ≠ 0) : coordinates (Tminus n hn) = some (-n,0) := rfl

@[simp] theorem T0_add_self (n : ℚ) (hn : n ≠ 0) : T0 n hn + T0 n hn = 0 := by
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY, congruentCurve, WeierstrassCurve.toAffine]

@[simp] theorem Tplus_add_self (n : ℚ) (hn : n ≠ 0) : Tplus n hn + Tplus n hn = 0 := by
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY, congruentCurve, WeierstrassCurve.toAffine]

@[simp] theorem Tminus_add_self (n : ℚ) (hn : n ≠ 0) : Tminus n hn + Tminus n hn = 0 := by
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY, congruentCurve, WeierstrassCurve.toAffine]

/-- Secant addition on the actual Mathlib point group, retaining both coordinates. -/
theorem coordinates_add_root {n x y t : ℚ} (hn : n ≠ 0)
    (hP : CongruentEquation n x y) (ht : CongruentEquation n t 0) (hxt : x ≠ t) :
    coordinates (finitePoint hn hP + finitePoint hn ht) =
      some ((y / (x-t)) ^ 2 - x - t,
        -(y / (x-t) * ((y / (x-t)) ^ 2 - x - t - x) + y)) := by
  unfold finitePoint
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxt]
  simp [coordinates, WeierstrassCurve.Affine.slope_of_X_ne hxt,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    congruentCurve, WeierstrassCurve.toAffine]

theorem coordinates_add_T0 {n x y : ℚ} (hn : n ≠ 0)
    (hP : CongruentEquation n x y) (hx : x ≠ 0) :
    coordinates (finitePoint hn hP + T0 n hn) =
      some (-n^2 / x, n^2 * y / x^2) := by
  rw [T0, coordinates_add_root hn hP _ hx]
  simp only [sub_zero]
  congr 1
  apply Prod.ext
  · dsimp
    dsimp [CongruentEquation] at hP
    field_simp
    nlinarith [hP]
  · dsimp
    dsimp [CongruentEquation] at hP
    field_simp
    linear_combination -y * hP

theorem coordinates_add_Tplus {n x y : ℚ} (hn : n ≠ 0)
    (hP : CongruentEquation n x y) (hx : x ≠ n) :
    coordinates (finitePoint hn hP + Tplus n hn) =
      some (n + 2*n^2 / (x-n), -(2*n^2*y) / (x-n)^2) := by
  rw [Tplus, coordinates_add_root hn hP _ hx]
  congr 1
  apply Prod.ext
  · dsimp
    dsimp [CongruentEquation] at hP
    field_simp
    nlinarith [hP]
  · dsimp
    dsimp [CongruentEquation] at hP
    field_simp
    linear_combination -y * hP

theorem coordinates_add_Tminus {n x y : ℚ} (hn : n ≠ 0)
    (hP : CongruentEquation n x y) (hx : x ≠ -n) :
    coordinates (finitePoint hn hP + Tminus n hn) =
      some (-n + 2*n^2 / (x+n), -(2*n^2*y) / (x+n)^2) := by
  have hxp : x + n ≠ 0 := by intro h; apply hx; linarith
  rw [Tminus, coordinates_add_root hn hP _ hx]
  simp only [sub_neg_eq_add]
  congr 1
  apply Prod.ext
  · dsimp
    dsimp [CongruentEquation] at hP
    field_simp [hxp]
    nlinarith [hP]
  · dsimp
    dsimp [CongruentEquation] at hP
    field_simp [hxp]
    linear_combination -y * hP

theorem coordinates_injective {n : ℚ} : Function.Injective (@coordinates n) := by
  intro P Q h
  cases P <;> cases Q <;> simp_all [coordinates]

@[simp] theorem Tplus_add_T0 (n : ℚ) (hn : n ≠ 0) :
    Tplus n hn + T0 n hn = Tminus n hn := by
  apply coordinates_injective
  rw [Tplus, coordinates_add_T0 hn _ hn, coordinates_Tminus]
  congr 1
  apply Prod.ext
  · dsimp
    field_simp
  · simp

@[simp] theorem T0_add_Tplus (n : ℚ) (hn : n ≠ 0) :
    T0 n hn + Tplus n hn = Tminus n hn := by rw [add_comm, Tplus_add_T0]

@[simp] theorem T0_add_Tminus (n : ℚ) (hn : n ≠ 0) :
    T0 n hn + Tminus n hn = Tplus n hn := by
  rw [← T0_add_Tplus n hn, ← add_assoc, T0_add_self, zero_add]

@[simp] theorem Tplus_add_Tminus (n : ℚ) (hn : n ≠ 0) :
    Tplus n hn + Tminus n hn = T0 n hn := by
  rw [← Tplus_add_T0 n hn, ← add_assoc, Tplus_add_self, zero_add]

/-- All rational points killed by two are exactly the four stated points. -/
theorem two_torsion_iff {n : ℚ} (hn : n ≠ 0) (P : Point n) :
    2 • P = 0 ↔ P = O n ∨ P = T0 n hn ∨ P = Tplus n hn ∨ P = Tminus n hn := by
  constructor
  · intro htwo
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
      have hadd : (WeierstrassCurve.Affine.Point.some x y h : Point n) +
          WeierstrassCurve.Affine.Point.some x y h = 0 := by simpa only [two_nsmul] using htwo
      have heq := eq_neg_of_add_eq_zero_left hadd
      rw [WeierstrassCurve.Affine.Point.neg_some] at heq
      have hy : y = -y := by
        simpa [WeierstrassCurve.Affine.negY, congruentCurve,
          WeierstrassCurve.toAffine] using (WeierstrassCurve.Affine.Point.some.inj heq).2
      have hy0 : y = 0 := by linarith
      have hcurve := (congruentEquation_iff_weierstrass n x y).mpr h.1
      have hprod : x * (x - n) * (x + n) = 0 := by
        simpa [CongruentEquation, hy0] using hcurve.symm
      rcases mul_eq_zero.mp hprod with hh | hh
      · rcases mul_eq_zero.mp hh with h0 | hp
        · exact Or.inr (Or.inl (coordinates_injective (by simp [coordinates, T0, finitePoint, h0, hy0])))
        · have hp0 : x = n := sub_eq_zero.mp hp
          exact Or.inr (Or.inr (Or.inl (coordinates_injective (by simp [coordinates, Tplus, finitePoint, hp0, hy0]))))
      · have hm0 : x = -n := by linarith
        exact Or.inr (Or.inr (Or.inr (coordinates_injective (by simp [coordinates, Tminus, finitePoint, hm0, hy0]))))
  · rintro (rfl | rfl | rfl | rfl) <;> simp [O, two_nsmul]

/-- The literal rational two-torsion subgroup. -/
def twoTorsion (n : ℚ) : AddSubgroup (Point n) := (nsmulAddMonoidHom 2).ker

@[simp] theorem mem_twoTorsion {n : ℚ} {P : Point n} :
    P ∈ twoTorsion n ↔ 2 • P = 0 := Iff.rfl

/-- The splitting used here is the existence part of the paper's direct sum.
It is enough to descend a globally divisible point into twice `H`. -/
def SplitsOverTwoTorsion (n : ℚ) (H : AddSubgroup (Point n)) : Prop :=
  ∀ P : Point n, ∃ h ∈ H, ∃ t : Point n, 2 • t = 0 ∧ P = h + t

/-- The paper's direct-sum hypothesis implies the decomposition used below. -/
theorem splitsOverTwoTorsion_of_isCompl {n : ℚ} {H : AddSubgroup (Point n)}
    (hcompl : IsCompl H (twoTorsion n)) : SplitsOverTwoTorsion n H := by
  intro P
  have hP : P ∈ H ⊔ twoTorsion n := by rw [hcompl.sup_eq_top]; trivial
  obtain ⟨h, hh, t, ht, heq⟩ := AddSubgroup.mem_sup.mp hP
  exact ⟨h, hh, t, ht, heq.symm⟩

theorem exists_double_in_subgroup {n : ℚ} {H : AddSubgroup (Point n)}
    (hsplit : SplitsOverTwoTorsion n H) {P : Point n}
    (hdouble : ∃ R : Point n, 2 • R = P) :
    ∃ Z ∈ H, 2 • Z = P := by
  obtain ⟨R, hR⟩ := hdouble
  obtain ⟨Z, hZ, t, ht, hRt⟩ := hsplit R
  refine ⟨Z, hZ, ?_⟩
  rw [hRt, nsmul_add, ht, add_zero] at hR
  exact hR

#print axioms nonsingular
#print axioms coordinates_add_T0
#print axioms coordinates_add_Tplus
#print axioms coordinates_add_Tminus
#print axioms two_torsion_iff
#print axioms splitsOverTwoTorsion_of_isCompl
#print axioms exists_double_in_subgroup

end FourCorner.CommonSource
