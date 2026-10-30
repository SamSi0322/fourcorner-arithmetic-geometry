import ThetaCoverClassPortable.ActualFiniteMapEuler
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
universe u
namespace FourCorner.ActualFiniteMapEuler

/-- Transport of the genuine finite-map Euler theorem along an actual scheme
isomorphism. The bundles and their algebraic-equivalence family are pulled
back by the specified map; no change of curve object is postulated. -/
theorem of_iso
    {k : Type u} [Field k] {A X : Scheme.{u}}
    (a : A ⟶ Spec (.of k)) [IsProper a] [Flat a]
    (ε : SchemeHomOver (𝟙 _) a) (F : SmoothProperCurve.FiniteMapData a ε)
    (x : X ⟶ Spec (.of k)) (e : A ≅ X) (he : e.hom ≫ x = a)
    (V : X.TwoAffineOpenCover) (L M : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (h0 : RelPicard.IsAlgEquivZero x L) :
    (Module.finrank k (V.sectionsOf x (L ⊗ M)).H0 : ℤ) -
      Module.finrank k (V.sectionsOf x (L ⊗ M)).H1 =
    (Module.finrank k (V.sectionsOf x M).H0 : ℤ) -
      Module.finrank k (V.sectionsOf x M).H1 := by
  let L' := (Scheme.Modules.pullback e.hom).obj L
  let M' := (Scheme.Modules.pullback e.hom).obj M
  obtain ⟨W, hW0, hW1, ⟨g0⟩, ⟨g1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso a x e he V
      (L ⊗ M) (L' ⊗ M') (Scheme.Modules.pullbackTensorObjIso e.hom L M).symm
  obtain ⟨W', hW'0, hW'1, ⟨m0⟩, ⟨m1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso a x e he V M M' (Iso.refl _)
  have hW : W' = W := by
    have h0 := hW'0.trans hW0.symm
    have h1 := hW'1.trans hW1.symm
    cases W'; cases W
    simp only at h0 h1
    subst h0; subst h1; rfl
  subst W'
  rw [← g0.finrank_eq, ← g1.finrank_eq, ← m0.finrank_eq, ← m1.finrank_eq]
  exact solution a ε F W L' M' (hL.pullback e.hom) (hM.pullback e.hom)
    (h0.pullback e.hom he)

/-- On the literal iterated fibre of c over an arbitrary test scheme, the
canonical pullback isomorphism supplies the finite-map Euler theorem. -/
theorem fibre
    {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of R)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε)
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R))
    {k : Type u} [Field k] (s : Spec (.of k) ⟶ T)
    (V : (pullback (pullback.snd c t) s).TwoAffineOpenCover)
    (L M : (pullback (pullback.snd c t) s).Modules)
    (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (h0 : RelPicard.IsAlgEquivZero (RelPicard.fibreAt c t s) L) :
    (Module.finrank k (V.sectionsOf (RelPicard.fibreAt c t s) (L ⊗ M)).H0 : ℤ) -
      Module.finrank k (V.sectionsOf (RelPicard.fibreAt c t s) (L ⊗ M)).H1 =
    (Module.finrank k (V.sectionsOf (RelPicard.fibreAt c t s) M).H0 : ℤ) -
      Module.finrank k (V.sectionsOf (RelPicard.fibreAt c t s) M).H1 := by
  letI : Algebra R k := (Spec.preimage (s ≫ t)).hom.toAlgebra
  have hx : Scheme.TwoAffineOpenCover.specMap R k = s ≫ t := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage (s ≫ t)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let e : pullback (pullback.snd c t) s ≅
      pullback c (Scheme.TwoAffineOpenCover.specMap R k) :=
    pullbackLeftPullbackSndIso c t s ≪≫ pullback.congrHom rfl hx.symm
  have he : e.hom ≫ SmoothProperCurve.baseChange R c k = RelPicard.fibreAt c t s := by
    simp only [e, Iso.trans_hom, Category.assoc, SmoothProperCurve.baseChange,
      pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_snd, RelPicard.fibreAt]
  have hei : e.inv ≫ RelPicard.fibreAt c t s = SmoothProperCurve.baseChange R c k := by
    rw [← he, Iso.inv_hom_id_assoc]
  exact of_iso (SmoothProperCurve.baseChange R c k) (SmoothProperCurve.sectionBaseChange k ε)
    (F.baseChange k) (RelPicard.fibreAt c t s) e.symm hei V L M hL hM h0

#print axioms of_iso
#print axioms fibre
end FourCorner.ActualFiniteMapEuler
