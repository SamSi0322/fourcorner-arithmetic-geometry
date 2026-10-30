import OppositePostProjectiveField
import SchemeFieldBaseChange

noncomputable section
namespace FourCorner.OppositeProjective.ExactGenus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct
open OppositePolynomials OppositeCoordinateAlgebra

abbrev V (mu nu : ℚ) := PostChart.twoAffineOpenCover mu nu

lemma cover0_nonempty (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    Nonempty (V mu nu).U0 := PostField.affineT_nonempty mu nu hn hp hl

lemma cover1_nonempty (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    Nonempty (V mu nu).U1 := by
  have hm : mu ≠ 0 := by intro h; simp [h] at hp
  letI := PostIntegral.pChart_isDomain hm hn (rational_A_ne_zero mu nu hn)
    (rational_B_ne_zero mu nu hn hp hl) (rational_S_ne_zero mu nu hn)
  exact Nonempty.map (Proj.basicOpenIsoSpec (quotientGrading mu nu) (PostIntegral.p mu nu)
    (PostIntegral.hp mu nu) one_pos).inv.base inferInstance

lemma cover01_nonempty (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    Nonempty ((V mu nu).U0 ⊓ (V mu nu).U1 : (curve mu nu).Opens) := by
  letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
  obtain ⟨x0⟩ := cover0_nonempty mu nu hn hp hl
  obtain ⟨x1⟩ := cover1_nonempty mu nu hn hp hl
  exact (nonempty_preirreducible_inter (V mu nu).U0.isOpen (V mu nu).U1.isOpen
    ⟨x0.1,x0.2⟩ ⟨x1.1,x1.2⟩).to_subtype

def fieldEquivAlg (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
    letI := SchemeFieldBaseChange.fieldAlgebra (toBase mu nu)
    functionField mu nu ≃ₐ[ℚ] (curve mu nu).functionField :=
  letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
  letI := SchemeFieldBaseChange.fieldAlgebra (toBase mu nu)
  (PostField.functionFieldEquiv mu nu hn hp hl).toRatAlgEquiv

lemma field_tensor_domain (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2)
    (L : Type) [Field L] [Algebra ℚ L] :
    letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
    letI := SchemeFieldBaseChange.fieldAlgebra (toBase mu nu)
    IsDomain (L ⊗[ℚ] (curve mu nu).functionField) := by
  letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
  letI := SchemeFieldBaseChange.fieldAlgebra (toBase mu nu)
  letI := OppositeAffineModel.rational_functionField_all_extensions_domain L mu nu hn hp hl
  let e : (L ⊗[ℚ] functionField mu nu) ≃ₐ[L] (L ⊗[ℚ] (curve mu nu).functionField) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) (fieldEquivAlg mu nu hn hp hl)
  exact Function.Injective.isDomain e.symm.toRingHom e.symm.injective

theorem geometricallyIntegral (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    GeometricallyIntegral (toBase mu nu) := by
  letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
  haveI := cover0_nonempty mu nu hn hp hl
  haveI := cover1_nonempty mu nu hn hp hl
  haveI := cover01_nonempty mu nu hn hp hl
  exact SchemeFieldBaseChange.geometricallyIntegral (toBase mu nu) (V mu nu)
    (fun L _ _ => field_tensor_domain mu nu hn hp hl L)

theorem geometricallyConnected (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    GeometricallyConnected (toBase mu nu) := by
  have h := geometricallyIntegral mu nu hn hp hl
  refine ⟨fun {L} _ y {Z} fst snd hpb => ?_⟩
  haveI := h.geometrically_isIntegral y fst snd hpb
  infer_instance

abbrev geometricScheme (mu nu : ℚ) :=
  pullback (toBase mu nu) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))
abbrev geometricToBase (mu nu : ℚ) :=
  pullback.snd (toBase mu nu) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))

lemma geometricIntegral (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    IsIntegral (geometricScheme mu nu) := by
  letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
  haveI := cover0_nonempty mu nu hn hp hl
  haveI := cover1_nonempty mu nu hn hp hl
  haveI := cover01_nonempty mu nu hn hp hl
  exact SchemeFieldBaseChange.isIntegral_pullback (toBase mu nu) (V mu nu) (AlgebraicClosure ℚ)
    (field_tensor_domain mu nu hn hp hl (AlgebraicClosure ℚ))


def geometricLiteralFunctionFieldEquiv (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
    letI := SchemeFieldBaseChange.fieldAlgebra (toBase mu nu)
    letI := geometricIntegral mu nu hn hp hl
    letI := (baseToFunctionField (geometricToBase mu nu)).toAlgebra
    letI := OppositeAffineModel.rational_all_field_extensions_integral (AlgebraicClosure ℚ) mu nu hn hp hl
    FractionRing ((AlgebraicClosure ℚ) ⊗[ℚ] ring mu nu) ≃ₐ[AlgebraicClosure ℚ]
      (geometricScheme mu nu).functionField := by
  letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
  letI := SchemeFieldBaseChange.fieldAlgebra (toBase mu nu)
  letI := geometricIntegral mu nu hn hp hl
  letI := (baseToFunctionField (geometricToBase mu nu)).toAlgebra
  letI := OppositeAffineModel.rational_all_field_extensions_integral (AlgebraicClosure ℚ) mu nu hn hp hl
  letI := OppositeAffineModel.rational_functionField_all_extensions_domain (AlgebraicClosure ℚ) mu nu hn hp hl
  letI := field_tensor_domain mu nu hn hp hl (AlgebraicClosure ℚ)
  haveI := cover0_nonempty mu nu hn hp hl
  haveI := cover1_nonempty mu nu hn hp hl
  haveI := cover01_nonempty mu nu hn hp hl
  let eT : ((AlgebraicClosure ℚ) ⊗[ℚ] functionField mu nu) ≃ₐ[AlgebraicClosure ℚ]
      ((AlgebraicClosure ℚ) ⊗[ℚ] (curve mu nu).functionField) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : (AlgebraicClosure ℚ) ≃ₐ[AlgebraicClosure ℚ] (AlgebraicClosure ℚ))
      (fieldEquivAlg mu nu hn hp hl)
  let e1 : FractionRing ((AlgebraicClosure ℚ) ⊗[ℚ] functionField mu nu) ≃ₐ[AlgebraicClosure ℚ]
      FractionRing ((AlgebraicClosure ℚ) ⊗[ℚ] (curve mu nu).functionField) :=
    IsFractionRing.algEquivOfAlgEquiv eT
  exact (HighGenus.tensorLiteralFractionEquiv mu nu hn hp hl (AlgebraicClosure ℚ)).trans
    (e1.trans (SchemeFieldBaseChange.pullbackFunctionFieldEquiv (toBase mu nu) (V mu nu)
      (AlgebraicClosure ℚ) (field_tensor_domain mu nu hn hp hl (AlgebraicClosure ℚ))))

/-- Genus five of the actual categorical Qbar pullback of the literal projective scheme. -/
theorem geometric_genus_five (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    letI := geometricIntegral mu nu hn hp hl
    letI := (baseToFunctionField (geometricToBase mu nu)).toAlgebra
    genusFF (AlgebraicClosure ℚ) (geometricScheme mu nu).functionField = 5 := by
  letI := PostIntegral.rational_literal_projective_integral mu nu hn hp hl
  letI := SchemeFieldBaseChange.fieldAlgebra (toBase mu nu)
  letI := geometricIntegral mu nu hn hp hl
  letI := (baseToFunctionField (geometricToBase mu nu)).toAlgebra
  letI := OppositeAffineModel.rational_all_field_extensions_integral (AlgebraicClosure ℚ) mu nu hn hp hl
  have hm : mu ≠ 0 := by intro h; simp [h] at hp
  exact (genusFF_eq_of_algEquiv (geometricLiteralFunctionFieldEquiv mu nu hn hp hl)).symm.trans
    (OppositeGeometricAffine.tensor_fraction_genus (L := AlgebraicClosure ℚ) hm hn
      (rational_A_ne_zero mu nu hn) (rational_B_ne_zero mu nu hn hp hl) (rational_S_ne_zero mu nu hn))

lemma geometricProper (mu nu : ℚ) : IsProper (geometricToBase mu nu) := by
  haveI := PostProper.toBase_isProper mu nu
  unfold geometricToBase
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma geometricSmooth (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    SmoothOfRelativeDimension 1 (geometricToBase mu nu) := by
  haveI := PostSmooth.literal_projective_smooth mu nu hn hp hl
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

/-- Geometric genus via the actual global relative Kahler sheaf on the actual pullback. -/
theorem geometric_globalDifferentials_five (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    let d := geometricToBase mu nu
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom d d.kaehler ⊤
    Module.Finite (AlgebraicClosure ℚ) Γ(d.kaehler,⊤) ∧
      Module.finrank (AlgebraicClosure ℚ) Γ(d.kaehler,⊤) = 5 := by
  let d := geometricToBase mu nu
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom d d.kaehler ⊤
  letI := geometricIntegral mu nu hn hp hl
  letI := geometricProper mu nu
  letI := geometricSmooth mu nu hn hp hl
  let W := (V mu nu).pullback (toBase mu nu) (AlgebraicClosure ℚ)
  obtain ⟨hfin,hrk⟩ := KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF W d
  exact ⟨hfin,hrk.trans (geometric_genus_five mu nu hn hp hl)⟩

/-- Exact paper proposition ell-opposite-genus on the genuine literal projective intersection.
Projectivity is witnessed by its actual closed immersion into P4, and geometric genus by
actual global Kahler differentials after the categorical Qbar base change. -/
theorem prop_ell_opposite_genus (mu nu : ℚ) (hn : nu ≠ 0) (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    IsClosedImmersion (embedding mu nu) ∧
    embedding mu nu ≫ spaceToBase = toBase mu nu ∧
    IsIntegral (curve mu nu) ∧ IsProper (toBase mu nu) ∧
    SmoothOfRelativeDimension 1 (toBase mu nu) ∧ GeometricallyConnected (toBase mu nu) ∧
    (let d := geometricToBase mu nu
     letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom d d.kaehler ⊤
     Module.Finite (AlgebraicClosure ℚ) Γ(d.kaehler,⊤) ∧
       Module.finrank (AlgebraicClosure ℚ) Γ(d.kaehler,⊤) = 5) :=
  ⟨embedding_isClosedImmersion mu nu, embedding_over mu nu,
    PostIntegral.rational_literal_projective_integral mu nu hn hp hl,
    PostProper.toBase_isProper mu nu, PostSmooth.literal_projective_smooth mu nu hn hp hl,
    geometricallyConnected mu nu hn hp hl, geometric_globalDifferentials_five mu nu hn hp hl⟩

end FourCorner.OppositeProjective.ExactGenus
#print axioms FourCorner.OppositeProjective.ExactGenus.geometricallyConnected
#print axioms FourCorner.OppositeProjective.ExactGenus.geometricIntegral

#print axioms FourCorner.OppositeProjective.ExactGenus.geometricLiteralFunctionFieldEquiv
#print axioms FourCorner.OppositeProjective.ExactGenus.geometric_globalDifferentials_five
#print axioms FourCorner.OppositeProjective.ExactGenus.prop_ell_opposite_genus
