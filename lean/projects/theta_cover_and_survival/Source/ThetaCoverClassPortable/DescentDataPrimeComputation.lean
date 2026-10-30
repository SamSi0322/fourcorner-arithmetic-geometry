import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
universe t v' v u' u
namespace FourCorner.DescentDataPrimeComputation

/-- Opaque-pseudofunctor computation, avoiding expansion of the entire
Scheme module pseudofunctor when this identity is specialized. -/
theorem from_to_hom
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v',u'})
    {S : C} {ι : Type t} {X : ι → C} (g : ∀i,X i ⟶ S)
    (sq : ∀i j,ChosenPullback (g i) (g j))
    (sq₃ : ∀i j k,ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L : F.obj (.mk (op S))) (i j : ι) :
    ((Pseudofunctor.DescentData'.fromDescentDataFunctor F sq sq₃).obj
      ((F.toDescentData g).obj L)).hom i j =
      (F.mapComp' (g i).op.toLoc (sq i j).p₁.op.toLoc (sq i j).p.op.toLoc
        (congrArg (fun z => z.op.toLoc) (sq i j).hp₁)).inv.toNatTrans.app L ≫
      (F.mapComp' (g j).op.toLoc (sq i j).p₂.op.toLoc (sq i j).p.op.toLoc
        (congrArg (fun z => z.op.toLoc) (sq i j).hp₂)).hom.toNatTrans.app L := by
  rfl

end FourCorner.DescentDataPrimeComputation
