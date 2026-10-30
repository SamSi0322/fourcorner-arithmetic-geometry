import CommonGenus17Field
import geometry.QuadraticRescaledUnit
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap

noncomputable section
namespace FourCorner.CommonGenus17Unramified
open AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

lemma ord_add_of_lt (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f < v.ord g) : v.ord (f+g) = v.ord f := by
  have hv : v.adicValuation g < v.adicValuation f := by
    rw [v.adicValuation_eq_exp_neg_ord hf, v.adicValuation_eq_exp_neg_ord hg,
      WithZero.exp_lt_exp]
    omega
  unfold Place.ord
  rw [v.adicValuation.map_add_eq_of_lt_left hv]

lemma ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  simp only [Place.ord, Valuation.map_neg]

/-- Every even radicand order is removed by an actual local uniformizer power. -/
theorem unramified_of_even_order {E : Type*} [Field E] [Algebra K E]
    [Algebra F E] [IsScalarTower K F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] [CharZero K] (w : Place K E) {a : F} {r : E}
    (hr : r^2 = algebraMap F E a) (hgen : Algebra.adjoin F {r} = ⊤)
    (ha : a ≠ 0) (heven : Even ((w.restrict F).ord a)) :
    w.ramificationIndex F = 1 := by
  obtain ⟨n,hn⟩ := heven
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible (w.restrict F).toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπord := (w.restrict F).ord_coe_irreducible hπ
  apply QuadraticRescaledUnit.ramificationIndex_eq_one_of_ord_eq_twice w hr hgen ha
    (zpow_ne_zero n hπ0)
  rw [(w.restrict F).ord_zpow, hπord, mul_one, hn]
  ring

variable (K : Type*) [Field K] [CharZero K]


def ell (t : K) : CommonLiteralField.field K t :=
  algebraMap (RatFunc K) (CommonLiteralField.field K t) RatFunc.X

theorem ell_ne_zero (t : K) : ell K t ≠ 0 :=
  (_root_.map_ne_zero _).mpr RatFunc.X_ne_zero

theorem rootP_sq (t : K) : (CommonLiteralField.root K t 0)^2 =
    ell K t + algebraMap K (CommonLiteralField.field K t) (t+1) := by
  rw [CommonLiteralField.root_sq]
  simp only [CommonLiteralField.radicand, map_add, ell,
    ← IsScalarTower.algebraMap_apply K (RatFunc K) (CommonLiteralField.field K t)]

theorem rootM_sq (t : K) : (CommonLiteralField.root K t 2)^2 =
    algebraMap K (CommonLiteralField.field K t) (t-1) *
      (algebraMap K (CommonLiteralField.field K t) (t+1)-ell K t) / ell K t := by
  rw [CommonLiteralField.root_sq]
  simp only [CommonLiteralField.radicand, map_div₀, map_mul, map_sub, ell,
    ← IsScalarTower.algebraMap_apply K (RatFunc K) (CommonLiteralField.field K t)]

/-- Actual orders at all places of the original four-radical field are even,
including every place over ell=0 and infinity. -/
theorem ell_ord_even {t : K} (ht1 : t ≠ 1) (htm : t ≠ -1)
    (v : Place K (CommonLiteralField.field K t)) : Even (v.ord (ell K t)) := by
  have hs : t-1 ≠ 0 := sub_ne_zero.mpr ht1
  have hT : t+1 ≠ 0 := by intro h; apply htm; linear_combination h
  have hTe : algebraMap K (CommonLiteralField.field K t) (t+1) ≠ 0 :=
    (_root_.map_ne_zero _).mpr hT
  have hse : algebraMap K (CommonLiteralField.field K t) (t-1) ≠ 0 :=
    (_root_.map_ne_zero _).mpr hs
  have hTord := v.ord_algebraMap (t+1)
  have hsord := v.ord_algebraMap (t-1)
  rcases lt_trichotomy (v.ord (ell K t)) 0 with hneg | hzero | hpos
  · have hsum := ord_add_of_lt v (ell_ne_zero K t) hTe (by omega)
    have hp := v.ord_zpow (CommonLiteralField.root K t 0) (2 : ℤ)
    rw [zpow_ofNat, rootP_sq, hsum] at hp
    exact ⟨v.ord (CommonLiteralField.root K t 0), by omega⟩
  · rw [hzero]
    exact ⟨0, by simp⟩
  · have hdiff : v.ord (algebraMap K (CommonLiteralField.field K t) (t+1) - ell K t) = 0 := by
      have h := ord_add_of_lt v hTe (neg_ne_zero.mpr (ell_ne_zero K t))
        (by rw [ord_neg]; omega)
      simpa only [sub_eq_add_neg, hTord] using h
    have hdiff0 : algebraMap K (CommonLiteralField.field K t) (t+1) - ell K t ≠ 0 := by
      intro hz
      have he : ell K t = algebraMap K (CommonLiteralField.field K t) (t+1) := by
        linear_combination -hz
      rw [he,hTord] at hpos
      omega
    have hm := v.ord_zpow (CommonLiteralField.root K t 2) (2 : ℤ)
    rw [zpow_ofNat, rootM_sq,
      QuadraticRescaledUnit.ord_div v (mul_ne_zero hse hdiff0) (ell_ne_zero K t),
      v.ord_mul hse hdiff0, hsord, hdiff] at hm
    exact ⟨-v.ord (CommonLiteralField.root K t 2), by omega⟩

namespace Extension
open CommonGenus17Field

theorem radical_integral (t κ : K) : IsIntegral (CommonLiteralField.field K t)
    (radical K t κ) := by
  refine ⟨Polynomial.X^2-Polynomial.C (radicand K t κ),
    Polynomial.monic_X_pow_sub_C _ (by decide), ?_⟩
  simp [radical_sq]

instance finiteDimensional (t κ : K) :
    FiniteDimensional (CommonLiteralField.field K t) (field K t κ) :=
  IntermediateField.adjoin.finiteDimensional (radical_integral K t κ)

instance charZeroBase (t : K) : CharZero (CommonLiteralField.field K t) :=
  charZero_of_injective_algebraMap (algebraMap K (CommonLiteralField.field K t)).injective

def root (t κ : K) : field K t κ :=
  ⟨radical K t κ, IntermediateField.subset_adjoin _ _ (by simp)⟩

theorem root_sq (t κ : K) : root K t κ ^ 2 =
    algebraMap (CommonLiteralField.field K t) (field K t κ) (radicand K t κ) := by
  apply Subtype.ext
  exact radical_sq K t κ

theorem root_generates (t κ : K) : Algebra.adjoin (CommonLiteralField.field K t)
    {root K t κ} = ⊤ := by
  have hg : IntermediateField.adjoin (CommonLiteralField.field K t) {root K t κ} = ⊤ := by
    apply IntermediateField.lift_injective (field K t κ)
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl
  apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic _).mp hg
  have hi := (IsIntegral.of_finite (CommonLiteralField.field K t) (root K t κ)).isAlgebraic
  simpa using hi

/-- The literal double extension has actual ramification index one at every
place, with no exceptional affine or boundary places omitted. -/
theorem all_places_unramified {t κ : K} (ht1 : t ≠ 1) (htm : t ≠ -1)
    (hκ : κ ≠ 0) (w : Place K (field K t κ)) :
    w.ramificationIndex (CommonLiteralField.field K t) = 1 := by
  have hk : algebraMap K (CommonLiteralField.field K t) κ ≠ 0 :=
    (_root_.map_ne_zero _).mpr hκ
  have heq : radicand K t κ = ell K t /
      algebraMap K (CommonLiteralField.field K t) κ := by
    simp only [radicand, ell, map_div₀,
      ← IsScalarTower.algebraMap_apply K (RatFunc K) (CommonLiteralField.field K t)]
  apply unramified_of_even_order w (root_sq K t κ) (root_generates K t κ)
  · rw [heq]
    exact div_ne_zero (ell_ne_zero K t) hk
  · rw [heq, QuadraticRescaledUnit.ord_div _ (ell_ne_zero K t) hk,
      Place.ord_algebraMap, sub_zero]
    exact ell_ord_even K ht1 htm _

end Extension

#print axioms Extension.all_places_unramified
#print axioms ell_ord_even
#print axioms unramified_of_even_order
end FourCorner.CommonGenus17Unramified
