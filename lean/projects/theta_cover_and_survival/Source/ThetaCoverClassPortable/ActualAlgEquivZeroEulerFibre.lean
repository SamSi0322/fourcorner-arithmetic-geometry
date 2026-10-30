import ThetaCoverClassPortable.ActualAlgEquivZeroEulerIff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
universe u
namespace FourCorner.ActualAlgEquivZeroEulerIff

/-- Transport to an actual isomorphic curve, retaining its chosen bundle and cover.
The actual finite map stays on its constructed original curve. -/
theorem of_iso
    {k : Type u} [Field k] [IsAlgClosed k] {A X : Scheme.{u}}
    (a : A ⟶ Spec (.of k)) [IsProper a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a]
    (ε : SchemeHomOver (𝟙 _) a) (F : SmoothProperCurve.FiniteMapData a ε)
    (x : X ⟶ Spec (.of k)) (e : A ≅ X) (he : e.hom ≫ x = a)
    (V : X.TwoAffineOpenCover) (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) :
    RelPicard.IsAlgEquivZero x L ↔
    (Module.finrank k (V.sectionsOf x L).H0 : ℤ) - Module.finrank k (V.sectionsOf x L).H1 =
    (Module.finrank k (V.sectionsOf x (𝟙_ X.Modules)).H0 : ℤ) - Module.finrank k (V.sectionsOf x (𝟙_ X.Modules)).H1 := by
  let L' := (Scheme.Modules.pullback e.hom).obj L
  obtain ⟨W,hW0,hW1,⟨l0⟩,⟨l1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso a x e he V L L' (Iso.refl _)
  obtain ⟨W',hW'0,hW'1,⟨u0⟩,⟨u1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso a x e he V (𝟙_ X.Modules)
      (𝟙_ A.Modules) (Scheme.Modules.pullbackTensorUnitObjIso e.hom).symm
  have hW : W'=W := twoAffineOpenCover_ext (hW'0.trans hW0.symm) (hW'1.trans hW1.symm)
  subst W'
  rw [←l0.finrank_eq,←l1.finrank_eq,←u0.finrank_eq,←u1.finrank_eq]
  constructor
  · intro h
    exact (solution a ε F L' (hL.pullback _) W).mp (h.pullback e.hom he)
  · intro hχ
    have h0 := (solution a ε F L' (hL.pullback _) W).mpr hχ
    have hi : e.inv ≫ a = x := by rw [←he,Iso.inv_hom_id_assoc]
    have hback := h0.pullback e.inv hi
    exact RelPicard.IsAlgEquivZero.of_iso
      ((Scheme.Modules.pullbackComp e.inv e.hom).app L ≪≫
       (Scheme.Modules.pullbackCongr e.inv_hom_id).app L ≪≫
       (Scheme.Modules.pullbackId X).app L) hback

/-- Every literal iterated algebraically closed test fibre, from the actual
original finite-map datum; no fibre FMD or target cut is a caller premise. -/
theorem fibre
    {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of R)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε)
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R))
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ T)
    (V : (pullback (pullback.snd c t) s).TwoAffineOpenCover)
    (L : (pullback (pullback.snd c t) s).Modules) (hL : Scheme.Modules.IsInvertible L) :
    RelPicard.IsAlgEquivZero (RelPicard.fibreAt c t s) L ↔
    (Module.finrank k (V.sectionsOf (RelPicard.fibreAt c t s) L).H0 : ℤ) -
      Module.finrank k (V.sectionsOf (RelPicard.fibreAt c t s) L).H1 =
    (Module.finrank k (V.sectionsOf (RelPicard.fibreAt c t s) (𝟙_ _)).H0 : ℤ) -
      Module.finrank k (V.sectionsOf (RelPicard.fibreAt c t s) (𝟙_ _)).H1 := by
  letI : Algebra R k := (Spec.preimage (s ≫ t)).hom.toAlgebra
  have hx : Scheme.TwoAffineOpenCover.specMap R k = s ≫ t := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage (s ≫ t)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let e : pullback (pullback.snd c t) s ≅ pullback c (Scheme.TwoAffineOpenCover.specMap R k) :=
    pullbackLeftPullbackSndIso c t s ≪≫ pullback.congrHom rfl hx.symm
  have he : e.hom ≫ SmoothProperCurve.baseChange R c k = RelPicard.fibreAt c t s := by
    simp only [e,Iso.trans_hom,Category.assoc,SmoothProperCurve.baseChange,pullback.congrHom_hom,
      pullback.lift_snd,Category.comp_id,pullbackLeftPullbackSndIso_hom_snd,RelPicard.fibreAt]
  have hei : e.inv ≫ RelPicard.fibreAt c t s = SmoothProperCurve.baseChange R c k := by
    rw [←he,Iso.inv_hom_id_assoc]
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact of_iso (SmoothProperCurve.baseChange R c k) (SmoothProperCurve.sectionBaseChange k ε)
    (F.baseChange k) (RelPicard.fibreAt c t s) e.symm hei V L hL

#print axioms of_iso
#print axioms fibre
end FourCorner.ActualAlgEquivZeroEulerIff
