import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Parity

namespace FourCorner

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem common_root_37_finite_check :
    ∀ t ell : ZMod 37,
      (t = 14 ∨ t = -14 ∨ t = 16 ∨ t = -16) → ell ≠ 0 →
      IsSquare (ell + t + 1) → IsSquare (ell - t + 1) →
      IsSquare ((t - 1) * (t + 1 - ell) / ell) →
      IsSquare ((t + 1) * (ell + t - 1) / ell) → IsSquare ell := by
  decide +kernel

/-- The finite-field core of the local square-class restriction at 37.
All four radicands are allowed to vanish. -/
theorem common_root_37_finite {t ell : ZMod 37}
    (ht : t = 14 ∨ t = 16) (hell : ell ≠ 0)
    (hP : IsSquare (ell + t + 1)) (hC : IsSquare (ell - t + 1))
    (hM : IsSquare ((t - 1) * (t + 1 - ell) / ell))
    (hB : IsSquare ((t + 1) * (ell + t - 1) / ell)) :
    IsSquare ell :=
  common_root_37_finite_check t ell (ht.elim Or.inl (fun h => Or.inr (Or.inr (Or.inl h))))
    hell hP hC hM hB

/-- The same finite-field restriction includes both signs of the two parameters. -/
theorem common_root_37_finite_signed {t ell : ZMod 37}
    (ht : t = 14 ∨ t = -14 ∨ t = 16 ∨ t = -16) (hell : ell ≠ 0)
    (hP : IsSquare (ell + t + 1)) (hC : IsSquare (ell - t + 1))
    (hM : IsSquare ((t - 1) * (t + 1 - ell) / ell))
    (hB : IsSquare ((t + 1) * (ell + t - 1) / ell)) :
    IsSquare ell :=
  common_root_37_finite_check t ell ht hell hP hC hM hB

/-- The successor is a nonsquare for either positive residue in the local test. -/
theorem common_root_37_successor_nonsquare {t : ZMod 37}
    (ht : t = 14 ∨ t = 16) : ¬ IsSquare (t + 1) := by
  rcases ht with rfl | rfl <;> decide

/-- Nonsquareness of the successor also holds for both negative residues. -/
theorem common_root_37_successor_nonsquare_signed {t : ZMod 37}
    (ht : t = 14 ∨ t = -14 ∨ t = 16 ∨ t = -16) : ¬ IsSquare (t + 1) := by
  rcases ht with rfl | rfl | rfl | rfl <;> decide

end FourCorner

#print axioms FourCorner.common_root_37_finite

#print axioms FourCorner.common_root_37_finite_signed
#print axioms FourCorner.common_root_37_successor_nonsquare
#print axioms FourCorner.common_root_37_successor_nonsquare_signed
