import Genus17Model

noncomputable section
namespace FourCorner.Genus17Geometry
open AlgebraicCurve
variable {K : Type*} [Field K] [CharZero K]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

theorem all_places_unramified (t κ : K) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0)
    (w : Place K (field t κ)) : w.ramificationIndex (baseField t) = 1 :=
  CommonGenus17Unramified.Extension.all_places_unramified K h1 hm hκ w

/-- Actual Riemann--Hurwitz genus of the literal five-root function field. -/
theorem genusFF_seventeen [IsAlgClosed K] (t κ : K)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    genusFF K (field t κ) = 17 := by
  letI : FiniteDimensional (RatFunc K) (baseField t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  letI := finite_over_line t κ h0 h1 hm
  letI : IsCurveOver K (baseField t) := RatFuncFiniteExtension.isCurveOver_of_charZero K (baseField t)
  letI : IsCurveOver K (field t κ) := RatFuncFiniteExtension.isCurveOver_of_charZero K (field t κ)
  have htame : ∀ w : Place K (field t κ), ((w.ramificationIndex (baseField t) : ℕ) : K) ≠ 0 := by
    intro w
    rw [all_places_unramified t κ h1 hm hκ w]
    norm_num
  have hrh := two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
    (RatFuncFiniteExtension.oneVariable K (baseField t)) htame
  have hsum : (∑ᶠ w : Place K (field t κ), ((w.ramificationIndex (baseField t) : ℤ)-1)) = 0 := by
    simp only [all_places_unramified t κ h1 hm hκ,Nat.cast_one,sub_self,finsum_zero]
  rw [degree_two t κ h0 h1 hm hκ, CommonLiteralField.genusFF_eq_nine h0 h1 hm,hsum] at hrh
  omega
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.all_places_unramified
#print axioms FourCorner.Genus17Geometry.genusFF_seventeen
