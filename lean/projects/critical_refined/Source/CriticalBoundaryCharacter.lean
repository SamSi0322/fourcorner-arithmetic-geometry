import CriticalProjectiveCharacter
import CriticalElliptic23
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

noncomputable section
set_option autoImplicit false
namespace FourCorner.CriticalBoundaryCharacter
variable {k : Type*} [Field k]

/-- Over the actual constants containing i, i and2 have the same squareclass. -/
theorem square_i_iff_two (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    IsSquare i ↔ IsSquare (2:k) := by
  have hi0:=CriticalElliptic23.iota_nonzero i hi
  have hs:IsSquare (2*i) := by
    refine ⟨1+i,?_⟩
    linear_combination -hi
  constructor
  · intro h
    have hh:=hs.div h
    simpa only [mul_div_cancel_right₀ _ hi0] using hh
  · intro h
    have hh:=hs.div h
    have he:(2*i)/(2:k)=i := by field_simp [h2]
    rwa [he] at hh

/-- Exact prime congruence criterion used by the normalized boundary fibres. -/
theorem square_i_iff_mod_eight {p:ℕ} [Fact p.Prime] (hmod:p%4=1)
    (i:ZMod p) (hi:i^2 = -1) : IsSquare i ↔ p%8=1 := by
  have hp2:p≠2 := by omega
  have h2:(2:ZMod p)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp2)
  rw [square_i_iff_two i hi h2,ZMod.exists_sq_eq_two_iff hp2]
  omega

end FourCorner.CriticalBoundaryCharacter
#print axioms FourCorner.CriticalBoundaryCharacter.square_i_iff_two
#print axioms FourCorner.CriticalBoundaryCharacter.square_i_iff_mod_eight
