import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.CurveRationalPlace07

/-- Any actual rational-valued homomorphism from a place valuation ring
forces its actual residue field to equal the rational constant field. -/
theorem isRational_of_eval {F : Type*} [Field F] [Algebra ℚ F]
    (w : Place ℚ F) (f : w.toValuationSubring →+* ℚ) : w.IsRational := by
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
  intro y
  refine ⟨g y, ?_⟩
  apply g.injective
  simp only [eq_ratCast,map_ratCast,Rat.cast_id]

/-- Exact identification of the local ring with the valuation ring furnished
by CurveModel.range_stalk_eq; no arbitrary place-point correspondence. -/
def stalkValuationEquiv {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (x : closedPoints M.C) :
    M.C.presheaf.stalk x.1 ≃+* (M.placeOfPoint x).toValuationSubring := by
  let g := M.ffEquiv.symm.toRingHom.comp
    (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)
  have hg : g.range = (M.placeOfPoint x).toValuationSubring.toSubring := M.range_stalk_eq x
  let f := g.codRestrict (M.placeOfPoint x).toValuationSubring
    (fun a => by
      change g a ∈ (M.placeOfPoint x).toValuationSubring.toSubring
      rw [← hg]; exact ⟨a,rfl⟩)
  apply RingEquiv.ofBijective f
  constructor
  · intro a b hab
    apply IsFractionRing.injective (M.C.presheaf.stalk x.1) M.C.functionField
    apply M.ffEquiv.symm.injective
    exact congrArg Subtype.val hab
  · intro y
    have hy : (y:F) ∈ g.range := by rw [hg]; exact y.property
    obtain ⟨a,ha⟩ := hy
    exact ⟨a, Subtype.ext ha⟩

/-- Every actual Q-point of any genuine smooth proper curve model gives
an actual rational place of its function field. -/
theorem point_gives_rational_place {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (p : Spec (CommRingCat.of ℚ) ⟶ M.C)
    (hp : p ≫ M.toBase = 𝟙 _) : ∃ w : Place ℚ F, w.IsRational := by
  let x : closedPoints M.C := ⟨p (IsLocalRing.closedPoint ℚ), by
    have := isClosedImmersion_of_comp_eq_id _ _ hp
    have hh := p.isClosedEmbedding.isClosed_range
    rwa [Set.range_eq_singleton] at hh
    exact fun a => congr(p $(Subsingleton.elim _ _))⟩
  let e := stalkValuationEquiv M x
  let f : (M.placeOfPoint x).toValuationSubring →+* ℚ :=
    (Scheme.stalkClosedPointTo p).hom.comp e.symm.toRingHom
  exact ⟨M.placeOfPoint x,isRational_of_eval _ f⟩

#print axioms point_gives_rational_place
end FourCorner.CurveRationalPlace07
