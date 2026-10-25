import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Even

set_option autoImplicit false

namespace FourCorner

/-- Reduction from modulus eight to parity. -/
abbrev dyadicMod8ToMod2 : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by decide) (ZMod 2)

/-- Reduction from modulus eight to modulus four. -/
abbrev dyadicMod8ToMod4 : ZMod 8 →+* ZMod 4 :=
  ZMod.castHom (by decide) (ZMod 4)

/-- The three possible square classes modulo eight, including zero. -/
def DyadicSquareResidue8 (s : ZMod 8) : Prop :=
  s = 0 ∨ s = 1 ∨ s = 4

instance (s : ZMod 8) : Decidable (DyadicSquareResidue8 s) :=
  inferInstanceAs (Decidable (s = 0 ∨ s = 1 ∨ s = 4))

/-- Every square modulo eight belongs to one of the three square classes. -/
theorem zmod8_square_residue (a : ZMod 8) : DyadicSquareResidue8 (a ^ 2) := by
  have h : ∀ a : ZMod 8, DyadicSquareResidue8 (a ^ 2) := by decide
  exact h a

/-- The square-class description also applies to an abstract square witness. -/
theorem zmod8_isSquare_residue {s : ZMod 8} (hs : IsSquare s) :
    DyadicSquareResidue8 s := by
  obtain ⟨a, rfl⟩ := hs
  simpa only [pow_two] using zmod8_square_residue a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem common_root_dyadic_finite_check :
    ∀ N X Y : ZMod 8,
      DyadicSquareResidue8 (X ^ 2 + Y ^ 2) →
      DyadicSquareResidue8 ((N - X) ^ 2 + Y ^ 2) →
      DyadicSquareResidue8 (X ^ 2 + (N - Y) ^ 2) →
      DyadicSquareResidue8 ((N - X) ^ 2 + (N - Y) ^ 2) →
      (dyadicMod8ToMod2 N ≠ 0 ∨ dyadicMod8ToMod2 X ≠ 0 ∨
        dyadicMod8ToMod2 Y ≠ 0) →
      dyadicMod8ToMod4 N = 0 ∧
      ((dyadicMod8ToMod2 X ≠ 0 ∧ dyadicMod8ToMod4 Y = 0) ∨
        (dyadicMod8ToMod4 X = 0 ∧ dyadicMod8ToMod2 Y ≠ 0)) ∧
      dyadicMod8ToMod2 (X ^ 2 + Y ^ 2) ≠ 0 ∧
      dyadicMod8ToMod2 ((N - X) ^ 2 + Y ^ 2) ≠ 0 ∧
      dyadicMod8ToMod2 (X ^ 2 + (N - Y) ^ 2) ≠ 0 ∧
      dyadicMod8ToMod2 ((N - X) ^ 2 + (N - Y) ^ 2) ≠ 0 := by
  decide

/-- A primitive normalized four-corner configuration of square distances
has side divisible by four, exactly one odd coordinate, and four odd square
distances. The finite computation only enumerates the three coordinates
modulo eight; square roots are removed through their square classes first. -/
theorem common_root_dyadic_finite {N X Y : ZMod 8}
    (h00 : IsSquare (X ^ 2 + Y ^ 2))
    (h10 : IsSquare ((N - X) ^ 2 + Y ^ 2))
    (h01 : IsSquare (X ^ 2 + (N - Y) ^ 2))
    (h11 : IsSquare ((N - X) ^ 2 + (N - Y) ^ 2))
    (hprim : dyadicMod8ToMod2 N ≠ 0 ∨ dyadicMod8ToMod2 X ≠ 0 ∨
      dyadicMod8ToMod2 Y ≠ 0) :
    dyadicMod8ToMod4 N = 0 ∧
    ((dyadicMod8ToMod2 X ≠ 0 ∧ dyadicMod8ToMod4 Y = 0) ∨
      (dyadicMod8ToMod4 X = 0 ∧ dyadicMod8ToMod2 Y ≠ 0)) ∧
    dyadicMod8ToMod2 (X ^ 2 + Y ^ 2) ≠ 0 ∧
    dyadicMod8ToMod2 ((N - X) ^ 2 + Y ^ 2) ≠ 0 ∧
    dyadicMod8ToMod2 (X ^ 2 + (N - Y) ^ 2) ≠ 0 ∧
    dyadicMod8ToMod2 ((N - X) ^ 2 + (N - Y) ^ 2) ≠ 0 :=
  common_root_dyadic_finite_check N X Y
    (zmod8_isSquare_residue h00) (zmod8_isSquare_residue h10)
    (zmod8_isSquare_residue h01) (zmod8_isSquare_residue h11) hprim

end FourCorner

#print axioms FourCorner.common_root_dyadic_finite
