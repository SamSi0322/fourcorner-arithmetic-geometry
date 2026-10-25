import FourCorner.CommonRoot37Finite
import FourCorner.CommonRoot37Unit
import FourCorner.CommonRootIntegralReduction

set_option autoImplicit false
namespace FourCorner

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

namespace CommonRootSource

/-- Manuscript lemma `common-37`: an integral parameter reducing to one of
`±14, ±16` forces the common coordinate of every actual nonzero four-root
source to be a square in Q_37. No valuation or residue-unit condition on
the source coordinate is assumed. -/
theorem ell_isSquare_37 (t : ℤ_[37])
    (S : CommonRootSource ℚ_[37] (t : ℚ_[37]))
    (ht : PadicInt.toZMod t=14 ∨ PadicInt.toZMod t= -14 ∨
      PadicInt.toZMod t=16 ∨ PadicInt.toZMod t= -16) : IsSquare S.ell := by
  have hns : ¬ IsSquare (PadicInt.toZMod (t+1)) := by
    simpa only [map_add,map_one] using common_root_37_successor_nonsquare_signed ht
  have hTbar : PadicInt.toZMod (t+1) ≠ 0 := by
    intro hz
    apply hns
    rw [hz]
    exact IsSquare.zero
  have hTnorm : ‖(t : ℚ_[37])+1‖=1 :=
    padicInt_norm_coe_eq_one_of_residue_ne_zero (t+1) hTbar
  have hTns : ¬ IsSquare ((t : ℚ_[37])+1) :=
    padicInt_not_isSquare_coe_of_residue (t+1) hns
  have hu : ‖S.ell‖=1 := S.ell_norm_one_of_nonsquare_T
    (by decide) t.2 hTnorm hTns
  obtain ⟨he,hP,hC,hM,hB⟩ := S.residue_squares_of_unit hu
  apply (padic_isSquare_iff_residue_of_norm_one (by decide) S.ell hu).mpr
  exact common_root_37_finite_signed ht he hP hC hM hB

/-- The same theorem stated for an arbitrary actual Q_37 parameter, with
integrality and reduction expressed by its norm and canonical residue. -/
theorem ell_isSquare_37_field {t : ℚ_[37]} (S : CommonRootSource ℚ_[37] t)
    (htint : ‖t‖ ≤ 1)
    (ht : padicResidue t htint=14 ∨ padicResidue t htint= -14 ∨
      padicResidue t htint=16 ∨ padicResidue t htint= -16) : IsSquare S.ell := by
  exact ell_isSquare_37 (padicIntegral t htint) S ht

end CommonRootSource
end FourCorner
#print axioms FourCorner.CommonRootSource.ell_isSquare_37
#print axioms FourCorner.CommonRootSource.ell_isSquare_37_field
