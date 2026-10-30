import OddFiveRamification
import CommonRamificationSum
import geometry.RatFuncFiniteExtension

noncomputable section
namespace FourCorner.OddResidueGenus
open AlgebraicCurve
variable {K : Type*} [Field K] [NeZero (2:K)] [IsAlgClosed K]
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

/-- RH genus nine for the actual four-root field over algebraically closed
constants of ANY characteristic different from two. -/
theorem four_genus {t : K} (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) :
    genusFF K (CommonLiteralField.field K t)=9 := by
  classical
  letI : PerfectField K := IsAlgClosed.perfectField K
  letI := ResidueRadicalField.four_finite K t
  letI := RadicalSeparable.four K t
  letI : IsCurveOver K (RatFunc K) := RatFuncFiniteExtension.isCurveOver_of_perfectField K (RatFunc K)
  letI : IsCurveOver K (CommonLiteralField.field K t) :=
    RatFuncFiniteExtension.isCurveOver_of_perfectField K (CommonLiteralField.field K t)
  have htame : ∀ w : Place K (CommonLiteralField.field K t),
      ((w.ramificationIndex (RatFunc K) : ℕ) : K)≠0 := by
    intro w
    rw [OddFourLiteral.index_formula h0 h1 hm w]
    split_ifs
    · exact NeZero.ne (2:K)
    · simpa only [Nat.cast_one] using (one_ne_zero : (1:K) ≠ 0)
  have hsum := CommonRamificationSum.finsum_ramificationIndex_sub_one_eq_fortyEight
    (OddFourPlaces.support t) (OddFourPlaces.support_card t h0 h1 hm)
    (ResidueRadicalDegree.four_degree K h0 h1 hm) (OddFourLiteral.index_formula h0 h1 hm)
  have hrh := two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
    (RatFuncFiniteExtension.base_oneVariable K) htame
  rw [ResidueRadicalDegree.four_degree K h0 h1 hm,
    RatFuncFiniteExtension.genus_base_eq_zero K,hsum] at hrh
  omega

/-- Genuine RH genus seventeen on the EXACT literal five-radical field,
with all ramification inputs proved in characteristic different from two. -/
theorem five_genus {t κ : K} (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0) :
    genusFF K (CommonGenus17Field.field K t κ)=17 := by
  classical
  letI : PerfectField K := IsAlgClosed.perfectField K
  letI := ResidueRadicalField.four_finite K t
  letI := ResidueRadicalField.fifth_finite K t κ
  letI := ResidueRadicalField.finite_over_line K t κ
  letI := OddFifthUnramified.fifth_separable K t κ
  letI : IsCurveOver K (CommonLiteralField.field K t) :=
    RatFuncFiniteExtension.isCurveOver_of_perfectField K (CommonLiteralField.field K t)
  letI : IsCurveOver K (CommonGenus17Field.field K t κ) := ResidueRadicalField.isCurveOver K t κ
  have he : ∀ w : Place K (CommonGenus17Field.field K t κ),
      w.ramificationIndex (CommonLiteralField.field K t)=1 :=
    fun w => (OddFifthUnramified.all_places K h1 hm hκ w).2
  have htame : ∀ w : Place K (CommonGenus17Field.field K t κ),
      ((w.ramificationIndex (CommonLiteralField.field K t) : ℕ) : K)≠0 := by
    intro w
    rw [he w]
    simpa only [Nat.cast_one] using (one_ne_zero : (1:K) ≠ 0)
  have hsum : (∑ᶠ w : Place K (CommonGenus17Field.field K t κ),
      ((w.ramificationIndex (CommonLiteralField.field K t) : ℤ)-1))=0 := by
    simp only [he,Nat.cast_one,sub_self,finsum_zero]
  have hrh := two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
    (RatFuncFiniteExtension.oneVariable K (CommonLiteralField.field K t)) htame
  rw [ResidueRadicalDegree.fifth_degree K h0 h1 hm hκ,four_genus h0 h1 hm,hsum] at hrh
  omega
end FourCorner.OddResidueGenus
#print axioms FourCorner.OddResidueGenus.four_genus
#print axioms FourCorner.OddResidueGenus.five_genus
