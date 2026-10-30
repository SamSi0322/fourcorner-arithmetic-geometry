import ThetaCoverClassPortable.SmoothCurveGenericIso
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FourCorner.SmoothCurveExtension
variable {K : Type u} [Field K]

def baseMap {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) : K →+* C.functionField :=
  (C.presheaf.germ ⊤ (genericPoint C) trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

abbrev fieldAlgebra {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) : Algebra K C.functionField :=
  (baseMap c).toAlgebra

theorem generic_comp_to_base {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) :
    C.fromSpecStalk (genericPoint C) ≫ c =
      Spec.map (CommRingCat.ofHom (baseMap c)) := by
  refine ext_of_isAffine ?_
  have h1 : (Spec.map (CommRingCat.ofHom (baseMap c))).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom (baseMap c) ≫
        (Scheme.ΓSpecIso (C.presheaf.stalk (genericPoint C))).inv := by
    rw [← Iso.inv_comp_eq]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  have h2 : CommRingCat.ofHom (baseMap c) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫
        C.presheaf.germ ⊤ (genericPoint C) trivial := by
    ext a
    rfl
  have h3 : (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)).op =
        𝟙 _ := by
    rw [show (homOfLE _).op = 𝟙 (Opposite.op ⊤) from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, h3, Category.comp_id, h1, h2]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]


/-- The only compatibility required by the generic extension is exactly the
base-field compatibility of the actual function-field algebra equivalence. -/
theorem iso_of_functionField_algEquiv {X Y : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) (d : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y]
    [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 1 d]
    [IsProper c] [IsProper d]
    (e : letI := fieldAlgebra c; letI := fieldAlgebra d;
      Y.functionField ≃ₐ[K] X.functionField) :
    letI := fieldAlgebra c; letI := fieldAlgebra d;
    ∃ i : X ≅ Y, i.hom ≫ d = c ∧
      X.fromSpecStalk (genericPoint X) ≫ i.hom =
        Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫
          Y.fromSpecStalk (genericPoint Y) := by
  letI := fieldAlgebra c
  letI := fieldAlgebra d
  apply iso_of_generic_equiv c d e.toRingEquiv
  rw [Category.assoc, generic_comp_to_base, generic_comp_to_base,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  exact e.commutes a

end FourCorner.SmoothCurveExtension
#print axioms FourCorner.SmoothCurveExtension.iso_of_functionField_algEquiv
