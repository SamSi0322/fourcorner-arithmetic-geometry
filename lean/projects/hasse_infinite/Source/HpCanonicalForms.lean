import HpRootOrders
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver

/-! Actual rational differentials on the four-root Hasse field. -/
namespace FourCorner.HpCanonicalForms
open AlgebraicCurve AlgebraicCurve.RationalFunctionField HpLiteralField HpFieldGeometry HpBranchPlaces
noncomputable section
variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
attribute [local instance] Classical.propDecidable
local instance perfect : PerfectField K := IsAlgClosed.perfectField K
local instance finite (p : K) : FiniteDimensional (RatFunc K) (field K p) := finite_over_line K p
local instance sep (p : K) : Algebra.IsSeparable (RatFunc K) (field K p) := separable K p
local instance baseCurve : IsCurveOver K (RatFunc K) := RatFuncFiniteExtension.isCurveOver_of_perfectField K (RatFunc K)
local instance fieldCurve (p : K) : IsCurveOver K (field K p) := isCurveOver K p
local instance baseFiniteType : Algebra.EssFiniteType K (RatFunc K) := RatFuncFiniteExtension.essFiniteType K (RatFunc K)
local instance fieldFiniteType (p : K) : Algebra.EssFiniteType K (field K p) := RatFuncFiniteExtension.essFiniteType K (field K p)
local instance baseCoord : ∀v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance fieldCoord (p : K) : ∀v : Place K (field K p), v.DCoordGenerates := dCoordGenerates_of_isCurveOver

abbrev lineDiff := P2MW.S_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.AlgebraicCurve.dX K

def rhoDiff (p : K) : Ω[field K p⁄K] := KaehlerDifferential.map K K (RatFunc K) (field K p) (lineDiff K)

theorem tame (p : K) (w : Place K (field K p)) : ((w.ramificationIndex (RatFunc K) : ℕ) : field K p) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.ne_of_gt w.ramificationIndex_pos)

theorem infinity_place_exists (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    ∃w : Place K (field K p), w.restrict (RatFunc K)=placeInfty K := by
  have hc : ((placeInfty K).fiberOver (field K p)).card=8 := by
    apply CommonRamificationSum.card_fiberOver_eq_eight (field_degree_sixteen K p hp ha hb)
    · intro w hw
      rw [HpGeometricGenus.actual_index_formula K p hp ha hb w,
        (placeInfty K).restrict_eq_of_mem_fiberOver hw,if_pos (show placeInfty K∈support K p from Finset.mem_insert_self _ _)]
    · intro w _
      exact CommonRamificationSum.inertiaDeg_eq_one w
  obtain ⟨w,hw⟩ := Finset.card_pos.mp (by omega : 0<((placeInfty K).fiberOver (field K p)).card)
  exact ⟨w,(placeInfty K).restrict_eq_of_mem_fiberOver hw⟩

theorem rhoDiff_ne_zero (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) : rhoDiff K p ≠ 0 := by
  obtain ⟨w,_⟩ := infinity_place_exists K p hp ha hb
  exact P2MW.S_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical.AlgebraicCurve.map_ne_zero_of_tame
    localUnitDerivativeRegular_of_isCurveOver (tame K p) w
    (P2MW.S_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.AlgebraicCurve.dX_ne_zero K)

theorem rhoDiff_order (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (w : Place K (field K p)) :
    w.ordDifferential (rhoDiff K p)=
      if w.restrict (RatFunc K)=placeInfty K then -3
      else if w.restrict (RatFunc K)∈support K p then 1 else 0 := by
  rw [rhoDiff,P2MW.S_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical.AlgebraicCurve.ordDifferential_map_eq
    localUnitDerivativeRegular_of_isCurveOver (tame K p)
    (P2MW.S_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.AlgebraicCurve.dX_ne_zero K)]
  by_cases hi : w.restrict (RatFunc K)=placeInfty K
  · rw [if_pos hi,hi,
      P2MW.S_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.AlgebraicCurve.ordDifferential_dX_placeInfty_of_perfectField,
      HpGeometricGenus.actual_index_formula K p hp ha hb,hi,if_pos (show placeInfty K∈support K p from Finset.mem_insert_self _ _)]
    norm_num
  · rw [if_neg hi,
      P2MW.S_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.AlgebraicCurve.ordDifferential_dX_of_ne_placeInfty_of_perfectField K hi,
      HpGeometricGenus.actual_index_formula K p hp ha hb]
    split_ifs <;> norm_num

def rootProduct (p : K) (s : Finset (Fin 4)) : field K p := ∏i∈s,root K p i

theorem rootProduct_ne_zero (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (s : Finset (Fin 4)) :
    rootProduct K p s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => HpRootOrders.root_ne_zero K p hp ha hb i

theorem rootProduct_order (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (w : Place K (field K p)) (s : Finset (Fin 4)) :
    w.ord (rootProduct K p s)=∑i∈s,w.ord (root K p i) := by
  induction s using Finset.induction_on with
  | empty => simp [rootProduct,w.ord_one]
  | @insert i s hi ih =>
    simp only [rootProduct,Finset.prod_insert hi,Finset.sum_insert hi] at *
    have hh := w.ord_mul (HpRootOrders.root_ne_zero K p hp ha hb i) (rootProduct_ne_zero K p hp ha hb s)
    simp only [rootProduct] at hh
    rw [hh,ih]

def form (p : K) (s : Finset (Fin 4)) : Ω[field K p⁄K] := (rootProduct K p s)⁻¹ • rhoDiff K p

theorem form_ne_zero (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (s : Finset (Fin 4)) :
    form K p s ≠ 0 := smul_ne_zero (inv_ne_zero (rootProduct_ne_zero K p hp ha hb s)) (rhoDiff_ne_zero K p hp ha hb)

theorem form_order (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (w : Place K (field K p)) (s : Finset (Fin 4)) :
    w.ordDifferential (form K p s)= -(∑i∈s,w.ord (root K p i))+w.ordDifferential (rhoDiff K p) := by
  rw [form,w.ordDifferential_smul (inv_ne_zero (rootProduct_ne_zero K p hp ha hb s))
    (w.differentialCoeff_ne_zero (rhoDiff_ne_zero K p hp ha hb)),w.ord_inv,rootProduct_order K p hp ha hb]

/-- Three or four distinct roots in the denominator give an actual globally regular differential. -/
theorem form_regular (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (s : Finset (Fin 4)) (hs : 3≤s.card) : form K p s ∈ regularDifferentials K (field K p) := by
  intro w
  refine ⟨w.differentialCoeff (form K p s),?_,(w.differentialCoeff_smul_dCoord _).symm⟩
  apply P2MW.S_AlgebraicCurve_finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed.GenusRegDiffs.mem_of_ord_nonneg w
  change 0≤w.ordDifferential (form K p s)
  rw [form_order K p hp ha hb,rhoDiff_order K p hp ha hb]
  by_cases hi : w.restrict (RatFunc K)=placeInfty K
  · rw [if_pos hi]
    simp only [HpRootOrders.at_infinity K p hp ha hb w hi,Finset.sum_const]
    simp only [nsmul_eq_mul,Int.cast_ofNat,mul_neg,mul_one,neg_neg]
    omega
  · rw [if_neg hi]
    by_cases hb0 : w.restrict (RatFunc K)∈support K p
    · rw [if_pos hb0]
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp ((Finset.mem_insert.mp hb0).resolve_left hi)
      have hj' : w.restrict (RatFunc K)=placeOfPoint K (branch K p j) := hj.symm
      simp only [HpRootOrders.at_branch K p hp ha hb w j hj']
      simp
      split_ifs <;> omega
    · rw [if_neg hb0]
      simp [HpRootOrders.off_support K p hp ha hb w hb0]

theorem regular_space_dimension (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    Module.Finite K (regularDifferentials K (field K p)) ∧
      Module.finrank K (regularDifferentials K (field K p))=5 := by
  rw [← P2MW.S_AlgebraicCurve_finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed.GenusRegDiffs.regularDiffs_eq]
  obtain ⟨hf,hg⟩ := finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed (K := K) (F := field K p)
  exact ⟨hf,hg.trans (HpGeometricGenus.genus_five K p hp ha hb)⟩

#print axioms infinity_place_exists
#print axioms rhoDiff_ne_zero
#print axioms rhoDiff_order
#print axioms form_ne_zero
#print axioms form_regular
#print axioms regular_space_dimension
end
end FourCorner.HpCanonicalForms
