import CurveRationalPlace07
import CommonActualBoundary
import CommonSchemeModel

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.CommonPostPointResidue
open CurveRationalPlace07 CommonRationalPlace
universe u

/-- Any actual rational scheme point is automatically over the rational base. -/
lemma point_overQ {F : Type u} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (p : Spec (.of ℚ) ⟶ M.C) : p ≫ M.toBase = 𝟙 _ := by
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

/-- The precise closed point underlying the supplied scheme-valued rational point. -/
def pointCenter {F : Type u} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (p : Spec (.of ℚ) ⟶ M.C) : closedPoints M.C :=
  ⟨p (IsLocalRing.closedPoint ℚ), by
    have := isClosedImmersion_of_comp_eq_id _ _ (point_overQ M p)
    have hh := p.isClosedEmbedding.isClosed_range
    rwa [Set.range_eq_singleton] at hh
    exact fun a => congr(p $(Subsingleton.elim _ _))⟩

abbrev pointPlace {F : Type u} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (p : Spec (.of ℚ) ⟶ M.C) := M.placeOfPoint (pointCenter M p)

def pointValuationEval {F : Type u} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (p : Spec (.of ℚ) ⟶ M.C) :
    (pointPlace M p).toValuationSubring →+* ℚ :=
  (Scheme.stalkClosedPointTo p).hom.comp (stalkValuationEquiv M (pointCenter M p)).symm.toRingHom

lemma pointPlace_rational {F : Type u} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (p : Spec (.of ℚ) ⟶ M.C) : (pointPlace M p).IsRational :=
  isRational_of_eval _ (pointValuationEval M p)

/-- The valuation-ring residue map attached to a rational scheme point is exactly
canonical rational-place evaluation, so boundary values cannot be lost in an existential place. -/
lemma valuation_eval_eq {F : Type u} [Field F] [Algebra ℚ F]
    (w : Place ℚ F) (hw : w.IsRational) (f : w.toValuationSubring →+* ℚ) :
    f = (rationalEval w hw).toRingHom := by
  have hsur : Function.Surjective f := by
    intro q
    refine ⟨algebraMap ℚ w.toValuationSubring q, ?_⟩
    exact congrArg (fun g : ℚ →+* ℚ => g q)
      (Subsingleton.elim (f.comp (algebraMap ℚ w.toValuationSubring)) (RingHom.id ℚ))
  have hker := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective f hsur)
  let g : w.ResidueField →+* ℚ := Ideal.Quotient.lift _ f (by
    intro a ha
    change a ∈ RingHom.ker f
    rwa [hker])
  have hg (a : w.toValuationSubring) : g (IsLocalRing.residue w.toValuationSubring a) = f a := rfl
  apply RingHom.ext
  intro a
  obtain ⟨q,hq⟩ := hw (IsLocalRing.residue w.toValuationSubring a)
  have hvalue : q = f a := by
    have h := congrArg g hq
    rw [hg] at h
    simpa only [eq_ratCast,map_ratCast,Rat.cast_id] using h
  rw [← hvalue]
  change q = (AlgEquiv.ofBijective (Algebra.ofId ℚ w.ResidueField)
    ⟨(algebraMap ℚ w.ResidueField).injective,hw⟩).symm (IsLocalRing.residue w.toValuationSubring a)
  rw [← hq]
  exact ((AlgEquiv.ofBijective (Algebra.ofId ℚ w.ResidueField)
    ⟨(algebraMap ℚ w.ResidueField).injective,hw⟩).symm.commutes q).symm

lemma stalkValuationEquiv_coe {F : Type u} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (x : closedPoints M.C) (a : M.C.presheaf.stalk x.1) :
    ((stalkValuationEquiv M x a : (M.placeOfPoint x).toValuationSubring) : F) =
      M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField a) := rfl

lemma stalkValuationEquiv_symm_image {F : Type u} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (x : closedPoints M.C) (a : (M.placeOfPoint x).toValuationSubring) :
    algebraMap (M.C.presheaf.stalk x.1) M.C.functionField ((stalkValuationEquiv M x).symm a) =
      M.ffEquiv (a : F) := by
  apply M.ffEquiv.symm.injective
  rw [RingEquiv.symm_apply_apply,← stalkValuationEquiv_coe]
  exact congrArg Subtype.val ((stalkValuationEquiv M x).apply_symm_apply a)

/-- Every actual rational point of D_t has a genuine local representative of ell,
whose pullback value avoids all finite omitted fibres. Regularity also excludes infinity. -/
theorem rational_point_ell_stalk_avoids_boundary (t : ℚ) (ht : 1 < t)
    (M : CurveModel ℚ (CommonLiteralField.field ℚ t)) (p : Spec (.of ℚ) ⟶ M.C) :
    ∃ a : M.C.presheaf.stalk (pointCenter M p).1,
      algebraMap (M.C.presheaf.stalk (pointCenter M p).1) M.C.functionField a =
        M.ffEquiv (CommonLiteralField.ell ℚ t) ∧
      (Scheme.stalkClosedPointTo p).hom a ∉ ({0,t-1,t+1,-(t-1),-(t+1)} : Finset ℚ) := by
  let w := pointPlace M p
  have hw : w.IsRational := pointPlace_rational M p
  have he := CommonLiteralField.ell_regular_at_rational_place t ht w hw
  let e := stalkValuationEquiv M (pointCenter M p)
  let a := e.symm ⟨CommonLiteralField.ell ℚ t,he⟩
  refine ⟨a,stalkValuationEquiv_symm_image M (pointCenter M p) _,?_⟩
  change pointValuationEval M p ⟨CommonLiteralField.ell ℚ t,he⟩ ∉ _
  rw [valuation_eval_eq w hw (pointValuationEval M p)]
  exact CommonLiteralField.rational_place_avoids_finite_boundary t ht w hw

end FourCorner.CommonPostPointResidue
#print axioms FourCorner.CommonPostPointResidue.valuation_eval_eq
#print axioms FourCorner.CommonPostPointResidue.rational_point_ell_stalk_avoids_boundary
