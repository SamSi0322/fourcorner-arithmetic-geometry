import OddQuadraticParity
import ResidueGenerators

noncomputable section
namespace FourCorner.OddFifthUnramified
open AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
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

variable (K : Type*) [Field K]


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

/-- The same literal fifth root equation, proved without CharZero. -/
theorem fifth_root_sq (t κ : K) : Genus17Geometry.fifthRoot t κ ^ 2 =
    algebraMap (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ)
      (CommonGenus17Field.radicand K t κ) := by
  apply Subtype.ext
  exact ResidueRadicalField.fifth_radical_sq K t κ

theorem fifth_separable [NeZero (2:K)] (t κ : K) :
    Algebra.IsSeparable (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ) := by
  have htwo : (2:CommonLiteralField.field K t) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K (CommonLiteralField.field K t))).mpr (NeZero.ne (2:K))
  exact RadicalSeparable.primitive (fifth_root_sq K t κ) (ResidueGenerators.fifth_root_generates K t κ) htwo

local instance fifthFinite (t κ : K) :
    FiniteDimensional (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ) :=
  ResidueRadicalField.fifth_finite K t κ
local instance fifthSeparable [NeZero (2:K)] (t κ : K) :
    Algebra.IsSeparable (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ) := fifth_separable K t κ

/-- At EVERY place, including those above zero and infinity, the original
fifth-root extension has unit different and ramification index one in any
characteristic different from two. -/
theorem all_places [NeZero (2:K)] {t κ : K} (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place K (CommonGenus17Field.field K t κ)) :
    differentIdeal (w.restrict (CommonLiteralField.field K t)).toValuationSubring
      (Place.integralClosureAt (CommonGenus17Field.field K t κ) (w.restrict (CommonLiteralField.field K t)))=⊤ ∧
    w.ramificationIndex (CommonLiteralField.field K t)=1 := by
  letI := ResidueRadicalField.fifth_finite K t κ
  have htwo : (2:CommonLiteralField.field K t) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K (CommonLiteralField.field K t))).mpr (NeZero.ne (2:K))
  letI : Algebra.IsSeparable (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ) :=
    RadicalSeparable.primitive (fifth_root_sq K t κ) (ResidueGenerators.fifth_root_generates K t κ) htwo
  have hk : algebraMap K (CommonLiteralField.field K t) κ ≠ 0 := (map_ne_zero _).mpr hκ
  have heq : CommonGenus17Field.radicand K t κ = ell K t /
      algebraMap K (CommonLiteralField.field K t) κ := by
    simp only [CommonGenus17Field.radicand,ell,map_div₀,
      ← IsScalarTower.algebraMap_apply K (RatFunc K) (CommonLiteralField.field K t)]
  apply OddQuadraticParity.even_order w (fifth_root_sq K t κ) (ResidueGenerators.fifth_root_generates K t κ)
  · rw [heq]
    exact div_ne_zero (ell_ne_zero K t) hk
  · rw [heq,QuadraticRescaledUnit.ord_div _ (ell_ne_zero K t) hk,Place.ord_algebraMap,sub_zero]
    exact ell_ord_even K h1 hm _
end FourCorner.OddFifthUnramified
#print axioms FourCorner.OddFifthUnramified.ell_ord_even
#print axioms FourCorner.OddFifthUnramified.all_places
