import FourCorner.CornerCharacterEncoding
import FourCorner.CornerAdjacentCharacter

set_option autoImplicit false
namespace FourCorner.IntegralModel

/-- The adjacent specialization of the master identity in the paper's
literal inert-prime valuation-product notation. -/
theorem adjacent_pair_reciprocity_literal_G (M : IntegralModel) (hX : Odd M.X)
    {i j : Bool × Bool} (hd : cornerDistanceSquared i j=1) :
    paperGInt ((M.cornerRadius i+M.cornerRadius j)/2) ^
        (1+e4 (M.cornerClass i*M.cornerClass j)) =
      (-1:ℤ)^(e4 (M.cornerClass i)*e4 (M.cornerClass j)) := by
  have hne : i ≠ j := by intro h; subst j; simp [cornerDistanceSquared] at hd
  simpa only [hd,sub_self,Int.toNat_zero,pow_zero,mul_one] using
    M.actual_pair_reciprocity_literal_G hX hne

end FourCorner.IntegralModel
#print axioms FourCorner.IntegralModel.adjacent_pair_reciprocity_literal_G
