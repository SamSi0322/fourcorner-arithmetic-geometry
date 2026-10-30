import OddFourLiteral
import OddFifthUnramified

noncomputable section
namespace FourCorner.OddFiveRamification
open AlgebraicCurve
variable {K : Type*} [Field K] [NeZero (2:K)]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
attribute [local instance] Classical.propDecidable
local instance finiteLine (t κ : K) : FiniteDimensional (RatFunc K) (CommonGenus17Field.field K t κ) :=
  ResidueRadicalField.finite_over_line K t κ

/-- The literal five-root cover has exactly the same six genuine branch
places as the four-root cover in every characteristic different from two. -/
theorem index_formula {t κ : K} (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place K (CommonGenus17Field.field K t κ)) :
    w.ramificationIndex (RatFunc K) = if w.restrict (RatFunc K) ∈ OddFourPlaces.support t then 2 else 1 := by
  letI := ResidueRadicalField.four_finite K t
  letI := ResidueRadicalField.fifth_finite K t κ
  letI := ResidueRadicalField.finite_over_line K t κ
  rw [PlaceTower.ramificationIndex_mul (F := RatFunc K) (E := CommonLiteralField.field K t) w,
    (OddFifthUnramified.all_places K h1 hm hκ w).2,one_mul,
    OddFourLiteral.index_formula h0 h1 hm (w.restrict (CommonLiteralField.field K t)),
    PlaceTower.restrict_restrict]

/-- Genuine tameness, expressed by the actual ramification index nonzero
in the constants. No characteristic-zero inference or degree premise is used. -/
theorem tame {t κ : K} (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place K (CommonGenus17Field.field K t κ)) :
    ((w.ramificationIndex (RatFunc K) : ℕ) : K) ≠ 0 := by
  rw [index_formula h0 h1 hm hκ w]
  split_ifs
  · exact NeZero.ne (2:K)
  · simpa only [Nat.cast_one] using (one_ne_zero : (1:K) ≠ 0)
end FourCorner.OddFiveRamification
#print axioms FourCorner.OddFiveRamification.index_formula
#print axioms FourCorner.OddFiveRamification.tame
