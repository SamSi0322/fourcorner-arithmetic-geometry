import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.StructuralGlobalSections

lemma appLE_top_eq_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.appLE ⊤ ⊤ le_top = f.appTop := by
  simp [Scheme.Hom.appLE]

/-- An actual over-base morphism commutes with the EXACT structure algebra maps. -/
theorem algebraMap_commutes {S : Type u} [CommRing S]
    {X Y : Scheme.{u}} (x : X ⟶ Spec (.of S)) (y : Y ⟶ Spec (.of S))
    (f : X ⟶ Y) (hf : f ≫ y = x) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom x ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom y ⊤
    ∀ s : S, f.appTop.hom (algebraMap S Γ(Y, ⊤) s) = algebraMap S Γ(X, ⊤) s := by
  intro s
  change f.appTop.hom
      ((y.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of S)).inv.hom s)) =
    (x.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of S)).inv.hom s)
  simp only [appLE_top_eq_appTop]
  rw [← hf, Scheme.Hom.comp_appTop]
  rfl

/-- The global-section map of an actual over-S isomorphism is an S-algebra equivalence. -/
def sectionsAlgEquiv {S : Type u} [CommRing S]
    {X Y : Scheme.{u}} (x : X ⟶ Spec (.of S)) (y : Y ⟶ Spec (.of S))
    (e : X ≅ Y) (he : e.hom ≫ y = x) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom x ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom y ⊤
    Γ(Y, ⊤) ≃ₐ[S] Γ(X, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom x ⊤
  letI := Scheme.TwoAffineOpenCover.algebraOfHom y ⊤
  let f : Γ(Y, ⊤) →ₐ[S] Γ(X, ⊤) :=
    { e.hom.appTop.hom with commutes' := algebraMap_commutes x y e.hom he }
  haveI : IsIso e.hom.appTop := by
    change IsIso (Scheme.Γ.map e.hom.op)
    infer_instance
  exact AlgEquiv.ofBijective f (ConcreteCategory.bijective_of_isIso e.hom.appTop)

/-- No field, flatness, nontriviality or connectedness premise is needed for
transport of exact structural global-function bijectivity through an over-S iso. -/
theorem bijective_algebraMap_of_overIso {S : Type u} [CommRing S]
    {X Y : Scheme.{u}} (x : X ⟶ Spec (.of S)) (y : Y ⟶ Spec (.of S))
    (e : X ≅ Y) (he : e.hom ≫ y = x)
    (hy : letI := Scheme.TwoAffineOpenCover.algebraOfHom y ⊤
      Function.Bijective (algebraMap S Γ(Y, ⊤))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom x ⊤
    Function.Bijective (algebraMap S Γ(X, ⊤)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom x ⊤
  letI := Scheme.TwoAffineOpenCover.algebraOfHom y ⊤
  let E := sectionsAlgEquiv x y e he
  have hcomp : algebraMap S Γ(X, ⊤) = E ∘ algebraMap S Γ(Y, ⊤) :=
    funext fun s => (E.commutes s).symm
  rw [hcomp]
  exact E.bijective.comp hy

end AlgebraicGeometry.Scheme.StructuralGlobalSections
