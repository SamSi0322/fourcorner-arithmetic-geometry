import ThetaCoverClassPortable.SmoothCurveGenericExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FourCorner.SmoothCurveExtension

private theorem spec_equiv_inverse {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := by
    ext a
    exact e.apply_symm_apply a
  rw [he, CommRingCat.ofHom_id, Spec.map_id]

/-- A base-compatible equivalence of the actual generic stalks extends to an
isomorphism of the original smooth proper integral curves over any field. -/
theorem iso_of_generic_equiv {K : Type u} [Field K] {X Y : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) (d : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y]
    [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 1 d]
    [IsProper c] [IsProper d]
    (e : Y.functionField ≃+* X.functionField)
    (he : (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y)) ≫ d =
      X.fromSpecStalk (genericPoint X) ≫ c) :
    ∃ i : X ≅ Y, i.hom ≫ d = c ∧
      X.fromSpecStalk (genericPoint X) ≫ i.hom =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y) := by
  let a := Spec.map (CommRingCat.ofHom e.toRingHom)
  let b := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hab : a ≫ b = 𝟙 _ := spec_equiv_inverse e
  have hba : b ≫ a = 𝟙 _ := spec_equiv_inverse e.symm
  have he' : (b ≫ X.fromSpecStalk (genericPoint X)) ≫ c =
      Y.fromSpecStalk (genericPoint Y) ≫ d := by
    calc
      (b ≫ X.fromSpecStalk (genericPoint X)) ≫ c =
          b ≫ (X.fromSpecStalk (genericPoint X) ≫ c) := Category.assoc _ _ _
      _ = b ≫ ((a ≫ Y.fromSpecStalk (genericPoint Y)) ≫ d) := by rw [← he]
      _ = Y.fromSpecStalk (genericPoint Y) ≫ d := by
        rw [← Category.assoc, ← Category.assoc, hba, Category.id_comp]
  obtain ⟨f, hfc, hf⟩ := extend_generic c d
    (a ≫ Y.fromSpecStalk (genericPoint Y)) he
  obtain ⟨g, hgd, hg⟩ := extend_generic d c
    (b ≫ X.fromSpecStalk (genericPoint X)) he'
  have hfg : f ≫ g = 𝟙 X := by
    apply hom_ext_generic c
    rw [← Category.assoc, hf, Category.assoc, hg,
      ← Category.assoc, hab]
    erw [Category.id_comp]
  have hgf : g ≫ f = 𝟙 Y := by
    apply hom_ext_generic d
    rw [← Category.assoc, hg, Category.assoc, hf,
      ← Category.assoc, hba]
    erw [Category.id_comp]
  exact ⟨⟨f,g,hfg,hgf⟩,hfc,hf⟩

end FourCorner.SmoothCurveExtension
#print axioms FourCorner.SmoothCurveExtension.iso_of_generic_equiv
