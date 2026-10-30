import CommonPostPointResidue
import CommonActualGenus
import CommonPostGeometricGenus

noncomputable section
open AlgebraicCurve AlgebraicCurve.RationalFunctionField
namespace FourCorner.CommonPostBoundaryPlaces
open CommonLiteralField CommonRationalPlace

local instance ratAlgebra : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
local instance ratModule : Module ℚ (RatFunc ℚ) := Algebra.toModule

/-- Genuine restriction of a rational-constant place, with its uniquely compatible Q scalar tower supplied. -/
def restrictToLine {F : Type} [Field F] [Algebra ℚ F] [Algebra (RatFunc ℚ) F]
    [Algebra.IsIntegral (RatFunc ℚ) F] (w : Place ℚ F) : Place ℚ (RatFunc ℚ) := by
  haveI : IsScalarTower ℚ (RatFunc ℚ) F :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact w.restrict (RatFunc ℚ)

lemma restrictToLine_eq {F : Type} [Field F] [Algebra ℚ F] [Algebra (RatFunc ℚ) F]
    [Algebra.IsIntegral (RatFunc ℚ) F] [IsScalarTower ℚ (RatFunc ℚ) F] (w : Place ℚ F) :
    restrictToLine w = w.restrict (RatFunc ℚ) := rfl

lemma ord_nonneg_of_regular {F : Type} [Field F] [Algebra ℚ F]
    (w : Place ℚ F) {f : F} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl|hf0
  · simp
  obtain ⟨p,hp⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨n,u,hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨f,hf⟩ : w.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hp
  have he : f = ((u:w.toValuationSubring):F)*((p:F)^(n:ℤ)) := by
    have h := congrArg Subtype.val hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [he,w.ord_unit_smul_zpow u hp (n:ℤ)]
  exact Int.natCast_nonneg n

lemma residue_eval_zero {F : Type} [Field F] [Algebra ℚ F]
    (w : Place ℚ F) (hw : w.IsRational) (a : w.toValuationSubring)
    (ha : a ∈ IsLocalRing.maximalIdeal w.toValuationSubring) : rationalEval w hw a = 0 := by
  change (AlgEquiv.ofBijective (Algebra.ofId ℚ w.ResidueField)
    ⟨(algebraMap ℚ w.ResidueField).injective,hw⟩).symm (IsLocalRing.residue w.toValuationSubring a) = 0
  rw [(IsLocalRing.residue_eq_zero_iff a).mpr ha,map_zero]

lemma finite_value_of_restrict (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    (w : Place ℚ (field ℚ t)) (hw : w.IsRational)
    (he : ell ℚ t ∈ w.toValuationSubring) (a : ℚ)
    (hv : w.restrict (RatFunc ℚ) = placeOfPoint ℚ a) :
    rationalEval w hw ⟨ell ℚ t,he⟩ = a := by
  letI : FiniteDimensional (RatFunc ℚ) (field ℚ t) :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_field_eq_sixteen ℚ h0 h1 hm]; norm_num)
  haveI : IsScalarTower ℚ (RatFunc ℚ) (field ℚ t) :=
    ⟨fun a b c => by simp [Algebra.smul_def, Rat.smul_def, map_ratCast, map_mul, mul_assoc]⟩
  have hfield : algebraMap (RatFunc ℚ) (field ℚ t) (CommonFourPlaceOrders.linear a) =
      ell ℚ t-algebraMap ℚ (field ℚ t) a := by
    rw [CommonFourPlaceOrders.linear_eq,map_sub,← IsScalarTower.algebraMap_apply]
    rfl
  have hne : ell ℚ t-algebraMap ℚ (field ℚ t) a ≠ 0 := by
    rw [← hfield]
    exact (map_ne_zero _).mpr (CommonFourPlaceOrders.linear_ne_zero a)
  have ho : 0 < w.ord (ell ℚ t-algebraMap ℚ (field ℚ t) a) := by
    rw [← hfield,w.ord_restrict,hv,CommonFourPlaceOrders.ord_linear_finite]
    simp only [ite_true, mul_one]
    exact_mod_cast w.ramificationIndex_pos (F := RatFunc ℚ)
  have hmem : ell ℚ t-algebraMap ℚ (field ℚ t) a ∈ w.toValuationSubring :=
    w.toValuationSubring.sub_mem he (w.algebraMap_mem' a)
  have hz := residue_eval_zero w hw ⟨ell ℚ t-algebraMap ℚ (field ℚ t) a,hmem⟩
    ((w.mem_maximalIdeal_iff_ord_pos hne hmem).mpr ho)
  have hsub : (⟨ell ℚ t-algebraMap ℚ (field ℚ t) a,hmem⟩ : w.toValuationSubring) =
      ⟨ell ℚ t,he⟩-algebraMap ℚ w.toValuationSubring a := Subtype.ext rfl
  rw [hsub,map_sub,AlgHom.commutes] at hz
  exact sub_eq_zero.mp hz

/-- Every actual rational place avoids the exact six branch places of the ell-line. -/
theorem rational_place_restrict_avoids_support (t : ℚ) (ht : 1 < t)
    (w : Place ℚ (field ℚ t)) (hw : w.IsRational) :
    w.restrict (RatFunc ℚ) ∉ CommonFourPlaceOrders.support t := by
  have h0 : t ≠ 0 := by linarith
  have h1 : t ≠ 1 := ne_of_gt ht
  have hm : t ≠ -1 := by linarith
  letI : FiniteDimensional (RatFunc ℚ) (field ℚ t) :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_field_eq_sixteen ℚ h0 h1 hm]; norm_num)
  haveI : IsScalarTower ℚ (RatFunc ℚ) (field ℚ t) :=
    ⟨fun a b c => by simp [Algebra.smul_def, Rat.smul_def, map_ratCast, map_mul, mul_assoc]⟩
  have he := ell_regular_at_rational_place t ht w hw
  have hav := rational_place_avoids_finite_boundary t ht w hw
  intro hs
  simp only [CommonFourPlaceOrders.support,Finset.mem_insert] at hs
  rcases hs with hi|hz|hb
  · have ho := w.ord_restrict (CommonFourPlaceOrders.linear (0:ℚ))
    rw [hi,CommonFourPlaceOrders.ord_linear_infty] at ho
    have hx : algebraMap (RatFunc ℚ) (field ℚ t) (CommonFourPlaceOrders.linear (0:ℚ)) = ell ℚ t := by
      rw [CommonFourPlaceOrders.linear_eq,map_zero,sub_zero]; rfl
    rw [hx] at ho
    have hn := ord_nonneg_of_regular w he
    have hp := w.ramificationIndex_pos (F := RatFunc ℚ)
    omega
  · have hval := finite_value_of_restrict t h0 h1 hm w hw he 0 hz
    apply hav
    rw [hval]
    simp
  · obtain ⟨i,hi⟩ := (CommonFourPlaceOrders.mem_privatePlaces t _).mp hb
    have hval := finite_value_of_restrict t h0 h1 hm w hw he (CommonFourPlaceOrders.branch t i) hi.symm
    apply hav
    rw [hval]
    fin_cases i <;> simp [CommonFourPlaceOrders.branch]

/-- Boundary exclusion retains the precise place of each actual scheme rational point. -/
theorem rational_point_place_avoids_boundary (t : ℚ) (ht : 1 < t)
    (M : CurveModel ℚ (field ℚ t)) (p : AlgebraicGeometry.Spec (.of ℚ) ⟶ M.C) :
    (CommonPostPointResidue.pointPlace M p).restrict (RatFunc ℚ) ∉ CommonFourPlaceOrders.support t :=
  rational_place_restrict_avoids_support t ht _ (CommonPostPointResidue.pointPlace_rational M p)


theorem rational_point_avoids_forAlgebra (t : ℚ) (ht : 1 < t)
    (a : Algebra ℚ (field ℚ t)) :
    letI := a
    ∀ (M : CurveModel ℚ (field ℚ t)) (p : AlgebraicGeometry.Spec (.of ℚ) ⟶ M.C),
      restrictToLine (CommonPostPointResidue.pointPlace M p) ∉ CommonFourPlaceOrders.support t := by
  have ha : a = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  subst a
  intro M p
  haveI : IsScalarTower ℚ (RatFunc ℚ) (field ℚ t) :=
    ⟨fun a b c => by simp [Algebra.smul_def, Rat.smul_def, map_ratCast, map_mul, mul_assoc]⟩
  rw [restrictToLine_eq]
  exact rational_point_place_avoids_boundary t ht M p

end FourCorner.CommonPostBoundaryPlaces
#print axioms FourCorner.CommonPostBoundaryPlaces.rational_place_restrict_avoids_support
#print axioms FourCorner.CommonPostBoundaryPlaces.rational_point_place_avoids_boundary


#print axioms FourCorner.CommonPostBoundaryPlaces.rational_point_avoids_forAlgebra
