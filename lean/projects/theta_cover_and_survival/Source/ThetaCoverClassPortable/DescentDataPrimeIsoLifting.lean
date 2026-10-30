import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe t v' v u' u
namespace FourCorner.DescentDataPrimeIsoLifting

/-- Lifting the computed descent isomorphism is performed with an abstract
pseudofunctor, before specializing to the actual scheme module pseudofunctor. -/
theorem nonempty_iso_of_components
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v',u'})
    {S : C} {ι : Type t} {X : ι → C} (g : ∀i,X i ⟶ S)
    (sq : ∀i j,ChosenPullback (g i) (g j))
    (sq₃ : ∀i j k,ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L₁ L₂ : F.obj (.mk (op S)))
    (e : ∀i, (F.map (g i).op.toLoc).toFunctor.obj L₁ ≅
      (F.map (g i).op.toLoc).toFunctor.obj L₂)
    (comm : ∀i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.map (e i).hom ≫
        ((Pseudofunctor.DescentData'.fromDescentDataFunctor F sq sq₃).obj
          ((F.toDescentData g).obj L₂)).hom i j =
      ((Pseudofunctor.DescentData'.fromDescentDataFunctor F sq sq₃).obj
          ((F.toDescentData g).obj L₁)).hom i j ≫
        (F.map (sq i j).p₂.op.toLoc).toFunctor.map (e j).hom)
    (h₁₂ : Function.Surjective ((F.toDescentData g).map (X := L₁) (Y := L₂)))
    (h₂₁ : Function.Surjective ((F.toDescentData g).map (X := L₂) (Y := L₁)))
    (h₁₁ : Function.Injective ((F.toDescentData g).map (X := L₁) (Y := L₁)))
    (h₂₂ : Function.Injective ((F.toDescentData g).map (X := L₂) (Y := L₂))) :
    Nonempty (L₁ ≅ L₂) := by
  let D₁ := (Pseudofunctor.DescentData'.fromDescentDataFunctor F sq sq₃).obj
    ((F.toDescentData g).obj L₁)
  let D₂ := (Pseudofunctor.DescentData'.fromDescentDataFunctor F sq sq₃).obj
    ((F.toDescentData g).obj L₂)
  let e' : D₁ ≅ D₂ := Pseudofunctor.DescentData'.isoMk e comm
  let E := Pseudofunctor.DescentData'.descentDataEquivalence F sq sq₃
  let ξ : (F.toDescentData g).obj L₁ ≅ (F.toDescentData g).obj L₂ :=
    (E.counitIso.app _).symm ≪≫ E.functor.mapIso e' ≪≫ E.counitIso.app _
  obtain ⟨ι₀,hι₀⟩ := h₁₂ ξ.hom
  obtain ⟨κ₀,hκ₀⟩ := h₂₁ ξ.inv
  refine ⟨⟨ι₀,κ₀,h₁₁ ?_,h₂₂ ?_⟩⟩
  · refine ((F.toDescentData g).map_comp ι₀ κ₀).trans ?_
    rw [hι₀,hκ₀,Iso.hom_inv_id]
    exact ((F.toDescentData g).map_id _).symm
  · refine ((F.toDescentData g).map_comp κ₀ ι₀).trans ?_
    rw [hι₀,hκ₀,Iso.inv_hom_id]
    exact ((F.toDescentData g).map_id _).symm

end FourCorner.DescentDataPrimeIsoLifting
