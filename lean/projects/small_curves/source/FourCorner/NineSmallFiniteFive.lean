import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Kernel-checked counts of the actual nonsingular point groups over `𝔽₅`.
The point at infinity is included by Mathlib's `Affine.Point` type. -/

namespace FourCorner.NineSmallFiniteFive

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩

/-- Reduction modulo five of `y² = x (x - 6) (x - 8)`. -/
def smallA : WeierstrassCurve (ZMod 5) := ⟨0, -14, 0, 48, 0⟩

/-- Reduction modulo five of `y² = x (x + 1) (x + 4)`. -/
def smallE0 : WeierstrassCurve (ZMod 5) := ⟨0, 5, 0, 4, 0⟩

instance smallA_isElliptic : smallA.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  change IsUnit (1 : ZMod 5)
  exact isUnit_one

instance smallE0_isElliptic : smallE0.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  change IsUnit (4 : ZMod 5)
  exact (ZMod.isUnit_iff_coprime 4 5).mpr (by decide)

theorem card_smallA : Nat.card smallA.toAffine.Point = 4 := by
  rw [Nat.card_congr smallA.toAffine.nonsingularPointEquiv]
  simp only [WeierstrassCurve.Affine.nonsingular_iff',
    WeierstrassCurve.Affine.equation_iff', smallA, WeierstrassCurve.toAffine, WithZero]
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_smallE0 : Nat.card smallE0.toAffine.Point = 8 := by
  rw [Nat.card_congr smallE0.toAffine.nonsingularPointEquiv]
  simp only [WeierstrassCurve.Affine.nonsingular_iff',
    WeierstrassCurve.Affine.equation_iff', smallE0, WeierstrassCurve.toAffine, WithZero]
  rw [Nat.card_eq_fintype_card]
  decide

instance finite_smallA : Finite smallA.toAffine.Point :=
  Nat.finite_of_card_ne_zero (by rw [card_smallA]; decide)

instance finite_smallE0 : Finite smallE0.toAffine.Point :=
  Nat.finite_of_card_ne_zero (by rw [card_smallE0]; decide)

theorem smallA_equation_iff_nonsingular (x y : ZMod 5) :
    smallA.toAffine.Equation x y ↔ smallA.toAffine.Nonsingular x y :=
  WeierstrassCurve.Affine.equation_iff_nonsingular

theorem smallE0_equation_iff_nonsingular (x y : ZMod 5) :
    smallE0.toAffine.Equation x y ↔ smallE0.toAffine.Nonsingular x y :=
  WeierstrassCurve.Affine.equation_iff_nonsingular

end FourCorner.NineSmallFiniteFive

#print axioms FourCorner.NineSmallFiniteFive.card_smallA
#print axioms FourCorner.NineSmallFiniteFive.card_smallE0
#print axioms FourCorner.NineSmallFiniteFive.smallA_isElliptic
#print axioms FourCorner.NineSmallFiniteFive.smallE0_isElliptic
