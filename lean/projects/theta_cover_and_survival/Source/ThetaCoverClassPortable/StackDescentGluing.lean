import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite
open CategoryTheory.Pseudofunctor LocallyDiscreteOpToCat
universe u v w w' t
namespace CategoryTheory.Pseudofunctor.DescentData
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w,w'})
  {Y' Y : C} (q : Y' ⟶ Y)

abbrev baseFamily {Z : C} (z : Z ⟶ Y) (_ : Unit) : pullback q z ⟶ Z := pullback.snd q z

abbrev basePull {Z : C} (z : Z ⟶ Y) :
    F.DescentData (fun _ : Unit => q) ⥤ F.DescentData (baseFamily q z) :=
  pullFunctor F (p:=z) (α:=fun i => i) (p':=fun _ : Unit => pullback.fst q z)
    (fun _ => pullback.condition)

abbrev baseMap {Z W : C} (z : Z ⟶ Y) (g : W ⟶ Z) : pullback q (g≫z) ⟶ pullback q z :=
  pullback.lift (pullback.fst q (g≫z)) (pullback.snd q (g≫z) ≫ g) (by
    simp only [Category.assoc,pullback.condition])

abbrev basePullMap {Z W : C} (z : Z ⟶ Y) (g : W ⟶ Z) :
    F.DescentData (baseFamily q z) ⥤ F.DescentData (baseFamily q (g≫z)) :=
  pullFunctor F (p:=g) (α:=fun i => i) (p':=fun _ : Unit => baseMap q z g)
    (fun _ => pullback.lift_snd _ _ _)

def basePullCompIso {Z W : C} (z : Z ⟶ Y) (g : W ⟶ Z) :
    basePull F q z ⋙ basePullMap F q z g ≅ basePull F q (g≫z) :=
  pullFunctorCompIso F (w := fun _ : Unit => pullback.condition)
    (r' := fun _ : Unit => pullback.fst q (g≫z))
    (fun _ : Unit => pullback.lift_snd _ _ _) (g≫z) rfl (fun _ => by simp [baseMap])

/-- Pull a genuine local effectiveness isomorphism to a further base change.
Both comparison factors are actual natural isomorphisms of descent functors. -/
def restrictIso {Z W : C} (z : Z ⟶ Y) (g : W ⟶ Z)
    (D : F.DescentData (fun _ : Unit => q)) (L : F.obj (.mk (op Z)))
    (e : (F.toDescentData (baseFamily q z)).obj L ≅ (basePull F q z).obj D) :
    (F.toDescentData (baseFamily q (g≫z))).obj ((F.map g.op.toLoc).toFunctor.obj L) ≅
      (basePull F q (g≫z)).obj D :=
  ((toDescentDataCompPullFunctorIso F
      (p:=g) (α:=fun i : Unit => i) (p':=fun _ => baseMap q z g)
      (fun _ => pullback.lift_snd _ _ _)).app L).symm ≪≫
    (basePullMap F q z g).mapIso e ≪≫ (basePullCompIso F q z g).app D

lemma restrictIso_hom_component {Z W : C} (z : Z ⟶ Y) (g : W ⟶ Z)
    (D : F.DescentData (fun _ : Unit => q)) (L : F.obj (.mk (op Z)))
    (e : (F.toDescentData (baseFamily q z)).obj L ≅ (basePull F q z).obj D) :
    (restrictIso F q z g D L e).hom.hom () =
      (F.mapComp' g.op.toLoc (pullback.snd q (g≫z)).op.toLoc
        (pullback.snd q (g≫z) ≫ g).op.toLoc (by simp)).inv.toNatTrans.app L ≫
      pullHom (e.hom.hom ()) (baseMap q z g)
        (pullback.snd q (g≫z) ≫ g) (pullback.fst q (g≫z))
        (by simp [baseMap]) (by simp [baseMap]) := by
  dsimp [restrictIso,basePullCompIso,toDescentDataCompPullFunctorIso,pullFunctorCompIso,isoMk,pullFunctor]
  rw [F.isoMapOfCommSq_eq _ _ rfl]
  dsimp [pullHom]
  simp only [Category.assoc]

/-- Transfer a local effectiveness isomorphism to any explicitly equal
base map; no equality of composites is suppressed. -/
def restrictIsoAlong {Z W : C} (z : Z ⟶ Y) (g : W ⟶ Z) (w : W ⟶ Y)
    (hw : g≫z=w) (D : F.DescentData (fun _ : Unit => q)) (L : F.obj (.mk (op Z)))
    (e : (F.toDescentData (baseFamily q z)).obj L ≅ (basePull F q z).obj D) :
    (F.toDescentData (baseFamily q w)).obj ((F.map g.op.toLoc).toFunctor.obj L) ≅
      (basePull F q w).obj D := by
  subst w
  exact restrictIso F q z g D L e

abbrev baseMapAlong {Z W : C} (z : Z ⟶ Y) (g : W ⟶ Z) (w : W ⟶ Y)
    (hw : g≫z=w) : pullback q w ⟶ pullback q z := by
  subst w
  exact baseMap q z g

lemma baseMapAlong_fst {Z W : C} (z : Z ⟶ Y) (g : W ⟶ Z) (w : W ⟶ Y) (hw : g≫z=w) :
    baseMapAlong q z g w hw ≫ pullback.fst q z = pullback.fst q w := by
  subst w
  exact pullback.lift_fst _ _ _

lemma baseMapAlong_snd {Z W : C} (z : Z ⟶ Y) (g : W ⟶ Z) (w : W ⟶ Y) (hw : g≫z=w) :
    baseMapAlong q z g w hw ≫ pullback.snd q z = pullback.snd q w ≫ g := by
  subst w
  exact pullback.lift_snd _ _ _

lemma baseMapAlong_comp {Z W X : C} (z : Z ⟶ Y) (g : W ⟶ Z) (w : W ⟶ Y)
    (hw : g≫z=w) (k : X ⟶ W) :
    baseMap q w k ≫ baseMapAlong q z g w hw =
      baseMapAlong q z (k≫g) (k≫w) (by rw [Category.assoc,hw]) := by
  apply pullback.hom_ext
  · rw [Category.assoc,baseMapAlong_fst,baseMapAlong_fst]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc,baseMapAlong_snd,baseMapAlong_snd,←Category.assoc]
    rw [show baseMap q w k ≫ pullback.snd q w = pullback.snd q (k≫w) ≫ k from pullback.lift_snd _ _ _]
    exact Category.assoc _ _ _

lemma baseMapAlong_section {Z W : C} (z : Z ⟶ Y) (g : W ⟶ Z) (w : W ⟶ Y)
    (hg : g≫z=w) (v : W ⟶ Y') (hv : v≫q=w) (a : W ⟶ pullback q z)
    (ha₁ : a≫pullback.fst q z=v) (ha₂ : a≫pullback.snd q z=g) :
    pullback.lift v (𝟙 W) (by simpa using hv) ≫ baseMapAlong q z g w hg = a := by
  apply pullback.hom_ext
  · rw [Category.assoc,baseMapAlong_fst,pullback.lift_fst]
    exact ha₁.symm
  · rw [Category.assoc,baseMapAlong_snd,←Category.assoc,pullback.lift_snd,Category.id_comp]
    exact ha₂.symm

lemma restrictIsoAlong_hom_component {Z W : C} (z : Z ⟶ Y) (g : W ⟶ Z) (w : W ⟶ Y)
    (hw : g≫z=w) (D : F.DescentData (fun _ : Unit => q)) (L : F.obj (.mk (op Z)))
    (e : (F.toDescentData (baseFamily q z)).obj L ≅ (basePull F q z).obj D) :
    (restrictIsoAlong F q z g w hw D L e).hom.hom () =
      (F.mapComp' g.op.toLoc (pullback.snd q w).op.toLoc
        (pullback.snd q w ≫ g).op.toLoc (by simp)).inv.toNatTrans.app L ≫
      pullHom (e.hom.hom ()) (baseMapAlong q z g w hw)
        (pullback.snd q w ≫ g) (pullback.fst q w)
        (baseMapAlong_snd q z g w hw) (baseMapAlong_fst q z g w hw) := by
  subst w
  exact restrictIso_hom_component F q z g D L e

lemma pullHom_comp_three {X₁ X₂ X₃ Z W : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {f₁ : Z ⟶ X₁} {f₂ : Z ⟶ X₂} {f₃ : Z ⟶ X₃}
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (b : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (g : W ⟶ Z) (g₁ : W ⟶ X₁) (g₂ : W ⟶ X₂) (g₃ : W ⟶ X₃)
    (h₁ : g≫f₁=g₁) (h₂ : g≫f₂=g₂) (h₃ : g≫f₃=g₃) :
    pullHom (a≫b) g g₁ g₃ h₁ h₃ = pullHom a g g₁ g₂ h₁ h₂ ≫ pullHom b g g₂ g₃ h₂ h₃ := by
  simp [pullHom,Functor.map_comp,Category.assoc]

lemma pullHom_map {X Z W : C} {M N : F.obj (.mk (op X))} (a : M ⟶ N)
    (g : Z ⟶ X) (h : W ⟶ Z) (hg : W ⟶ X) (hgh : h≫g=hg) :
    pullHom ((F.map g.op.toLoc).toFunctor.map a) h hg hg hgh hgh =
      (F.map hg.op.toLoc).toFunctor.map a := by
  let e := Cat.Hom.toNatIso (F.mapComp' g.op.toLoc h.op.toLoc hg.op.toLoc (by rw [←Quiver.Hom.comp_toLoc,←op_comp,hgh]))
  have H := e.hom.naturality a
  have H' := congrArg (fun f => f ≫ e.inv.app N) H
  simpa [e,pullHom,Category.assoc] using H'.symm

lemma hom_eq_of_pullHom_cover {Z X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {g : Z ⟶ X₁} {h : Z ⟶ X₂} {κ : Type t} {V : κ → C} (v : ∀ i,V i ⟶ Z)
    (hp : F.IsPrestackFor (Presieve.ofArrows V v))
    (a b : (F.map g.op.toLoc).toFunctor.obj M₁ ⟶ (F.map h.op.toLoc).toFunctor.obj M₂)
    (H : ∀ i,pullHom a (v i) (v i≫g) (v i≫h)=pullHom b (v i) (v i≫g) (v i≫h)) : a=b := by
  let FF := (F.isPrestackFor_ofArrows_iff v).mp hp |>.some
  apply FF.map_injective
  apply hom_ext
  intro i
  dsimp only [toDescentData_map_hom]
  rw [map_eq_pullHom a (v i) (v i≫g) (v i≫h) rfl rfl,
    map_eq_pullHom b (v i) (v i≫g) (v i≫h) rfl rfl,H i]

lemma hom_eq_of_pullHom_cover_chosen {Z X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {g : Z ⟶ X₁} {h : Z ⟶ X₂} {κ : Type t} {V : κ → C} (v : ∀ i,V i ⟶ Z)
    (hp : F.IsPrestackFor (Presieve.ofArrows V v))
    (a b : (F.map g.op.toLoc).toFunctor.obj M₁ ⟶ (F.map h.op.toLoc).toFunctor.obj M₂)
    (H : ∀ i,∃ (g' : V i ⟶ X₁) (h' : V i ⟶ X₂) (hg : v i≫g=g') (hh : v i≫h=h'),
      pullHom a (v i) g' h' hg hh=pullHom b (v i) g' h' hg hh) : a=b := by
  let FF := (F.isPrestackFor_ofArrows_iff v).mp hp |>.some
  apply FF.map_injective
  apply hom_ext
  intro i
  obtain ⟨g',h',hg,hh,H⟩ := H i
  dsimp only [toDescentData_map_hom]
  rw [map_eq_pullHom a (v i) g' h' hg hh,map_eq_pullHom b (v i) g' h' hg hh,H]

section LocalLifts
variable (P : ∀ X : C, F.obj (.mk (op X)) → Prop)
    (hPpull : ∀ (X Z : C) (g : Z ⟶ X) (M : F.obj (.mk (op X))),
      P X M → P Z ((F.map g.op.toLoc).toFunctor.obj M))
    (hff : ∀ (Z : C) (z : Z ⟶ Y) (M N : F.obj (.mk (op Z))), P Z M → P Z N →
      Function.Bijective ((F.toDescentData (baseFamily q z)).map : (M ⟶ N) → _))
    {ι : Type t} {U : ι → C} (f : ∀ i, U i ⟶ Y)
    (D : F.DescentData (fun _ : Unit => q))
    (L : ∀ i, F.obj (.mk (op (U i)))) (hL : ∀ i, P (U i) (L i))
    (e : ∀ i, (F.toDescentData (baseFamily q (f i))).obj (L i) ≅ (basePull F q (f i)).obj D)

/-- The unique genuine overlap morphism lifted by the supplied fully
faithful q-descent comparison. It is a morphism of original F-objects. -/
def overlapHom {Z : C} (z : Z ⟶ Y) (i j : ι) (g : Z ⟶ U i) (h : Z ⟶ U j)
    (hg : g≫f i=z) (hh : h≫f j=z) :
    (F.map g.op.toLoc).toFunctor.obj (L i) ⟶ (F.map h.op.toLoc).toFunctor.obj (L j) :=
  Function.surjInv (hff Z z _ _ (hPpull _ _ g _ (hL i)) (hPpull _ _ h _ (hL j))).2
    ((restrictIsoAlong F q (f i) g z hg D (L i) (e i)).hom ≫
      (restrictIsoAlong F q (f j) h z hh D (L j) (e j)).inv)

lemma overlapHom_map {Z : C} (z : Z ⟶ Y) (i j : ι) (g : Z ⟶ U i) (h : Z ⟶ U j)
    (hg : g≫f i=z) (hh : h≫f j=z) :
    (F.toDescentData (baseFamily q z)).map (overlapHom F q P hPpull hff f D L hL e z i j g h hg hh) =
      (restrictIsoAlong F q (f i) g z hg D (L i) (e i)).hom ≫
      (restrictIsoAlong F q (f j) h z hh D (L j) (e j)).inv :=
  Function.surjInv_eq _ _

lemma overlapHom_pull_square {Z : C} (z : Z ⟶ Y) (i j : ι) (g : Z ⟶ U i) (h : Z ⟶ U j)
    (hg : g≫f i=z) (hh : h≫f j=z) :
    pullHom (overlapHom F q P hPpull hff f D L hL e z i j g h hg hh) (pullback.snd q z)
      (pullback.snd q z ≫ g) (pullback.snd q z ≫ h) ≫
      pullHom ((e j).hom.hom ()) (baseMapAlong q (f j) h z hh)
        (pullback.snd q z ≫ h) (pullback.fst q z)
        (baseMapAlong_snd q (f j) h z hh) (baseMapAlong_fst q (f j) h z hh) =
      pullHom ((e i).hom.hom ()) (baseMapAlong q (f i) g z hg)
        (pullback.snd q z ≫ g) (pullback.fst q z)
        (baseMapAlong_snd q (f i) g z hg) (baseMapAlong_fst q (f i) g z hg) := by
  have heq := overlapHom_map F q P hPpull hff f D L hL e z i j g h hg hh
  have hh' : (F.toDescentData (baseFamily q z)).map
      (overlapHom F q P hPpull hff f D L hL e z i j g h hg hh) ≫
        (restrictIsoAlong F q (f j) h z hh D (L j) (e j)).hom =
          (restrictIsoAlong F q (f i) g z hg D (L i) (e i)).hom := by
    rw [heq]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have hcomp := congrArg (fun a => a.hom ()) hh'
  dsimp only [comp_hom, toDescentData_map_hom] at hcomp
  rw [restrictIsoAlong_hom_component,restrictIsoAlong_hom_component] at hcomp
  have H := congrArg (fun a =>
    (F.mapComp' g.op.toLoc (pullback.snd q z).op.toLoc
      (pullback.snd q z ≫ g).op.toLoc (by simp)).hom.toNatTrans.app (L i) ≫ a) hcomp
  simpa [pullHom,Category.assoc] using H

lemma overlapHom_total_square {Z : C} (z : Z ⟶ Y) (w : Z ⟶ Y') (hw : w≫q=z)
    (i j : ι) (g : Z ⟶ U i) (h : Z ⟶ U j) (hg : g≫f i=z) (hh : h≫f j=z)
    (a : Z ⟶ pullback q (f i)) (b : Z ⟶ pullback q (f j))
    (ha₁ : a≫pullback.fst q (f i)=w) (ha₂ : a≫pullback.snd q (f i)=g)
    (hb₁ : b≫pullback.fst q (f j)=w) (hb₂ : b≫pullback.snd q (f j)=h) :
    overlapHom F q P hPpull hff f D L hL e z i j g h hg hh ≫
      pullHom ((e j).hom.hom ()) b h w hb₂ hb₁ =
        pullHom ((e i).hom.hom ()) a g w ha₂ ha₁ := by
  let t : Z ⟶ pullback q z := pullback.lift w (𝟙 Z) (by simpa using hw)
  have H := congrArg (fun m => pullHom m t g w (by simp [t,Category.assoc]) (by simp [t]))
    (overlapHom_pull_square F q P hPpull hff f D L hL e z i j g h hg hh)
  rw [pullHom_comp_three F _ _ t g h w
    (by simp [t,Category.assoc]) (by simp [t,Category.assoc]) (by simp [t])] at H
  simp only [pullHom_pullHom] at H
  have ht₁ : t ≫ baseMapAlong q (f i) g z hg=a := baseMapAlong_section q (f i) g z hg w hw a ha₁ ha₂
  have ht₂ : t ≫ baseMapAlong q (f j) h z hh=b := baseMapAlong_section q (f j) h z hh w hw b hb₁ hb₂
  simpa only [ht₁,ht₂,show t ≫ pullback.snd q z=𝟙 Z from pullback.lift_snd _ _ _,pullHom_id] using H

lemma overlapHom_eq_of_map {Z : C} (z : Z ⟶ Y) (i j : ι) (g : Z ⟶ U i) (h : Z ⟶ U j)
    (hg : g≫f i=z) (hh : h≫f j=z)
    (a : (F.map g.op.toLoc).toFunctor.obj (L i) ⟶ (F.map h.op.toLoc).toFunctor.obj (L j))
    (ha : (F.toDescentData (baseFamily q z)).map a ≫
      (restrictIsoAlong F q (f j) h z hh D (L j) (e j)).hom =
        (restrictIsoAlong F q (f i) g z hg D (L i) (e i)).hom) :
    a = overlapHom F q P hPpull hff f D L hL e z i j g h hg hh := by
  apply (hff Z z _ _ (hPpull _ _ g _ (hL i)) (hPpull _ _ h _ (hL j))).1
  rw [overlapHom_map]
  apply (cancel_mono (restrictIsoAlong F q (f j) h z hh D (L j) (e j)).hom).mp
  simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using ha

lemma overlapHom_eq_of_square {Z : C} (z : Z ⟶ Y) (i j : ι) (g : Z ⟶ U i) (h : Z ⟶ U j)
    (hg : g≫f i=z) (hh : h≫f j=z)
    (a : (F.map g.op.toLoc).toFunctor.obj (L i) ⟶ (F.map h.op.toLoc).toFunctor.obj (L j))
    (ha : pullHom a (pullback.snd q z) (pullback.snd q z≫g) (pullback.snd q z≫h) ≫
      pullHom ((e j).hom.hom ()) (baseMapAlong q (f j) h z hh)
        (pullback.snd q z ≫ h) (pullback.fst q z)
        (baseMapAlong_snd q (f j) h z hh) (baseMapAlong_fst q (f j) h z hh) =
      pullHom ((e i).hom.hom ()) (baseMapAlong q (f i) g z hg)
        (pullback.snd q z ≫ g) (pullback.fst q z)
        (baseMapAlong_snd q (f i) g z hg) (baseMapAlong_fst q (f i) g z hg)) :
    a = overlapHom F q P hPpull hff f D L hL e z i j g h hg hh := by
  apply overlapHom_eq_of_map F q P hPpull hff f D L hL e z i j g h hg hh a
  apply hom_ext
  intro i'
  cases i'
  dsimp only [comp_hom,toDescentData_map_hom]
  rw [restrictIsoAlong_hom_component,restrictIsoAlong_hom_component]
  have H := congrArg (fun m =>
    (F.mapComp' g.op.toLoc (pullback.snd q z).op.toLoc
      (pullback.snd q z ≫ g).op.toLoc (by simp)).inv.toNatTrans.app (L i) ≫ m) ha
  simpa [pullHom,Category.assoc] using H

lemma overlapHom_pullHom_comp {Z W : C} (z : Z ⟶ Y) (k : W ⟶ Z)
    (i j : ι) (g : Z ⟶ U i) (h : Z ⟶ U j) (hg : g≫f i=z) (hh : h≫f j=z) :
    pullHom (overlapHom F q P hPpull hff f D L hL e z i j g h hg hh) k (k≫g) (k≫h) =
      overlapHom F q P hPpull hff f D L hL e (k≫z) i j (k≫g) (k≫h)
        (by rw [Category.assoc,hg]) (by rw [Category.assoc,hh]) := by
  apply overlapHom_eq_of_square F q P hPpull hff f D L hL e (k≫z) i j (k≫g) (k≫h)
  have H := congrArg (fun m => pullHom m (baseMap q z k)
    (pullback.snd q (k≫z) ≫ (k≫g)) (pullback.fst q (k≫z))
    (by simp [baseMap,Category.assoc]) (by simp [baseMap]))
    (overlapHom_pull_square F q P hPpull hff f D L hL e z i j g h hg hh)
  rw [pullHom_comp_three F _ _ (baseMap q z k)
    (pullback.snd q (k≫z) ≫ (k≫g)) (pullback.snd q (k≫z) ≫ (k≫h)) (pullback.fst q (k≫z))
    (by simp [baseMap,Category.assoc]) (by simp [baseMap,Category.assoc]) (by simp [baseMap])] at H
  simp only [pullHom_pullHom,baseMapAlong_comp] at H ⊢
  simpa [baseMap,Category.assoc] using H

lemma overlapHom_self {Z : C} (z : Z ⟶ Y) (i : ι) (g : Z ⟶ U i) (hg : g≫f i=z) :
    overlapHom F q P hPpull hff f D L hL e z i i g g hg hg = 𝟙 _ := by
  apply (hff Z z _ _ (hPpull _ _ g _ (hL i)) (hPpull _ _ g _ (hL i))).1
  rw [overlapHom_map,Functor.map_id,Iso.hom_inv_id]

lemma overlapHom_comp {Z : C} (z : Z ⟶ Y) (i j k : ι)
    (g : Z ⟶ U i) (h : Z ⟶ U j) (l : Z ⟶ U k)
    (hg : g≫f i=z) (hh : h≫f j=z) (hl : l≫f k=z) :
    overlapHom F q P hPpull hff f D L hL e z i j g h hg hh ≫
      overlapHom F q P hPpull hff f D L hL e z j k h l hh hl =
        overlapHom F q P hPpull hff f D L hL e z i k g l hg hl := by
  apply (hff Z z _ _ (hPpull _ _ g _ (hL i)) (hPpull _ _ l _ (hL k))).1
  rw [Functor.map_comp,overlapHom_map,overlapHom_map,overlapHom_map]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]

/-- Genuine local F-descent datum constructed from the given q-descent
object and local effective lifts. All pullback/cocycle axioms are proved. -/
def localLiftsDatum : F.DescentData f where
  obj := L
  hom Z z i j g h hg hh := overlapHom F q P hPpull hff f D L hL e z i j g h hg hh
  pullHom_hom W Z k z w hw i j g h hg hh kg kh hkg hkh := by
    subst w
    subst kg
    subst kh
    exact overlapHom_pullHom_comp F q P hPpull hff f D L hL e z k i j g h hg hh
  hom_self Z z i g hg := overlapHom_self F q P hPpull hff f D L hL e z i g hg
  hom_comp Z z i j k g h l hg hh hl := overlapHom_comp F q P hPpull hff f D L hL e z i j k g h l hg hh hl

/-- Actual evaluation functor on a descent datum. -/
def evaluate (i : ι) : F.DescentData f ⥤ F.obj (.mk (op (U i))) where
  obj A := A.obj i
  map a := a.hom i

def evaluateAny {κ : Type t} {S : C} {V : κ → C} (v : ∀ i, V i ⟶ S) (i : κ) :
    F.DescentData v ⥤ F.obj (.mk (op (V i))) where
  obj A := A.obj i
  map a := a.hom i

abbrev coverFamily (i : ι) : pullback q (f i) ⟶ Y' := pullback.fst q (f i)

abbrev coverPull : F.DescentData f ⥤ F.DescentData (coverFamily q f) :=
  pullFunctor F (p:=q) (α:=fun i => i) (p':=fun i => pullback.snd q (f i))
    (fun _ => pullback.condition.symm)

/-- The given local q-effectiveness maps form an actual isomorphism over
q's pulled-back cover, compatible with all overlap morphisms. -/
def localEffectivityIso :
    (coverPull F q f).obj (localLiftsDatum F q P hPpull hff f D L hL e) ≅
      (F.toDescentData (coverFamily q f)).obj (D.obj ()) :=
  isoMk (fun i => (evaluateAny F (baseFamily q (f i)) ()).mapIso (e i)) (by
    intro Z w i j a b ha hb
    have hg : (a≫pullback.snd q (f i))≫f i=w≫q := by
      rw [Category.assoc,←pullback.condition,←Category.assoc,ha]
    have hh : (b≫pullback.snd q (f j))≫f j=w≫q := by
      rw [Category.assoc,←pullback.condition,←Category.assoc,hb]
    have H := overlapHom_total_square F q P hPpull hff f D L hL e (w≫q) w rfl i j
      (a≫pullback.snd q (f i)) (b≫pullback.snd q (f j)) hg hh a b ha rfl hb rfl
    have H' := congrArg (fun m =>
      (F.mapComp (pullback.snd q (f i)).op.toLoc a.op.toLoc).inv.toNatTrans.app (L i) ≫ m ≫
      (F.mapComp' (pullback.fst q (f j)).op.toLoc b.op.toLoc w.op.toLoc (by rw [←Quiver.Hom.comp_toLoc,←op_comp,hb])).hom.toNatTrans.app (D.obj ())) H
    have hz : a ≫ pullback.fst q (f i) ≫ q=w≫q := by rw [←Category.assoc,ha]
    simpa [evaluateAny,localLiftsDatum,coverPull,coverFamily,ofObj,pullFunctor,pullFunctorObjHom,
      pullHom,mapComp'_eq_mapComp,Category.assoc,hz] using H'.symm)

def comparisonOnCover (M : F.obj (.mk (op Y)))
    (E : (F.toDescentData f).obj M ≅ localLiftsDatum F q P hPpull hff f D L hL e) :
    (F.toDescentData (coverFamily q f)).obj ((F.map q.op.toLoc).toFunctor.obj M) ≅
      (F.toDescentData (coverFamily q f)).obj (D.obj ()) :=
  ((toDescentDataCompPullFunctorIso F
    (p:=q) (α:=fun i => i) (p':=fun i => pullback.snd q (f i))
    (fun _ => pullback.condition.symm)).app M).symm ≪≫
    (coverPull F q f).mapIso E ≪≫ localEffectivityIso F q P hPpull hff f D L hL e

lemma comparison_component (M : F.obj (.mk (op Y)))
    (E : (F.toDescentData f).obj M ≅ localLiftsDatum F q P hPpull hff f D L hL e)
    (a : (F.map q.op.toLoc).toFunctor.obj M ≅ D.obj ())
    (ha : (F.toDescentData (coverFamily q f)).mapIso a = comparisonOnCover F q P hPpull hff f D L hL e M E)
    (i : ι) :
    (F.mapComp' q.op.toLoc (pullback.fst q (f i)).op.toLoc
      (pullback.fst q (f i)≫q).op.toLoc (by simp)).hom.toNatTrans.app M ≫
      (F.map (pullback.fst q (f i)).op.toLoc).toFunctor.map a.hom =
    (F.mapComp' (f i).op.toLoc (pullback.snd q (f i)).op.toLoc
      (pullback.fst q (f i)≫q).op.toLoc (by rw [←Quiver.Hom.comp_toLoc,←op_comp,pullback.condition])).hom.toNatTrans.app M ≫
      (F.map (pullback.snd q (f i)).op.toLoc).toFunctor.map (E.hom.hom i) ≫ (e i).hom.hom () := by
  have H := congrArg (fun a => a.hom.hom i) ha
  dsimp [comparisonOnCover,toDescentDataCompPullFunctorIso,isoMk,coverPull,pullFunctor,
    localEffectivityIso,evaluateAny] at H
  rw [F.isoMapOfCommSq_eq _ _ rfl] at H
  have H' := congrArg (fun m =>
    (F.mapComp' q.op.toLoc (pullback.fst q (f i)).op.toLoc
      (pullback.fst q (f i)≫q).op.toLoc (by simp)).hom.toNatTrans.app M ≫ m) H
  simpa [Category.assoc] using H'

def localGlobalIso (M : F.obj (.mk (op Y)))
    (E : (F.toDescentData f).obj M ≅ localLiftsDatum F q P hPpull hff f D L hL e) (i : ι) :
    (basePull F q (f i)).obj ((F.toDescentData (fun _ : Unit => q)).obj M) ≅
      (basePull F q (f i)).obj D :=
  (toDescentDataCompPullFunctorIso F
    (p:=f i) (α:=fun i : Unit => i) (p':=fun _ => pullback.fst q (f i))
    (fun _ => pullback.condition)).app M ≪≫
    (F.toDescentData (baseFamily q (f i))).mapIso ((evaluate F f i).mapIso E) ≪≫ e i

lemma comparison_local_component (M : F.obj (.mk (op Y)))
    (E : (F.toDescentData f).obj M ≅ localLiftsDatum F q P hPpull hff f D L hL e)
    (a : (F.map q.op.toLoc).toFunctor.obj M ≅ D.obj ())
    (ha : (F.toDescentData (coverFamily q f)).mapIso a = comparisonOnCover F q P hPpull hff f D L hL e M E)
    (i : ι) : (F.map (pullback.fst q (f i)).op.toLoc).toFunctor.map a.hom =
      (localGlobalIso F q P hPpull hff f D L hL e M E i).hom.hom () := by
  have H := congrArg (fun a => a.hom.hom i) ha
  dsimp [comparisonOnCover,toDescentDataCompPullFunctorIso,isoMk,coverPull,pullFunctor,
    localEffectivityIso,evaluateAny,localGlobalIso,evaluate]
  dsimp [comparisonOnCover,toDescentDataCompPullFunctorIso,isoMk,coverPull,pullFunctor,
    localEffectivityIso,evaluateAny] at H
  rw [F.isoMapOfCommSq_eq _ (pullback.fst q (f i)≫q).op.toLoc (by simp)] at H
  rw [F.isoMapOfCommSq_eq _ (pullback.fst q (f i)≫q).op.toLoc (by rw [←Quiver.Hom.comp_toLoc,←op_comp,←pullback.condition])]
  simpa [Category.assoc] using H

/-- Compatibility with q-descent is local for a cover whose every pullback
is a prestack cover. This glues MORPHISMS, without an object premise. -/
def homOfLocalCompatibility
    (hpre : ∀ (Z : C) (z : Z ⟶ Y), F.IsPrestackFor (Presieve.ofArrows _ (coverFamily z f)))
    (A B : F.DescentData (fun _ : Unit => q)) (a : A.obj () ⟶ B.obj ())
    (s : ∀ i,(basePull F q (f i)).obj A ⟶ (basePull F q (f i)).obj B)
    (hs : ∀ i,(s i).hom ()=(F.map (pullback.fst q (f i)).op.toLoc).toFunctor.map a) : A ⟶ B where
  hom _ := a
  comm Z z i j g h hg hh := by
    cases i
    cases j
    apply hom_eq_of_pullHom_cover_chosen F (coverFamily z f) (hpre Z z)
    intro i
    let p : pullback z (f i) ⟶ Z := pullback.fst z (f i)
    let t : pullback z (f i) ⟶ U i := pullback.snd z (f i)
    let ag : pullback z (f i) ⟶ pullback q (f i) :=
      pullback.lift (p≫g) t (by rw [Category.assoc,hg]; exact pullback.condition)
    let ah : pullback z (f i) ⟶ pullback q (f i) :=
      pullback.lift (p≫h) t (by rw [Category.assoc,hh]; exact pullback.condition)
    have H := (s i).comm (i₁:=()) (i₂:=()) t ag ah (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
    rw [hs i] at H
    dsimp [basePull,pullFunctor,pullFunctorObjHom] at H
    have H' := congrArg (fun m =>
      (F.mapComp (pullback.fst q (f i)).op.toLoc ag.op.toLoc).hom.toNatTrans.app (A.obj ()) ≫ m ≫
      (F.mapComp (pullback.fst q (f i)).op.toLoc ah.op.toLoc).inv.toNatTrans.app (B.obj ())) H
    have hgg : (ag≫pullback.fst q (f i))≫q=t≫f i := by
      rw [show ag≫pullback.fst q (f i)=p≫g from pullback.lift_fst _ _ _,Category.assoc,hg]
      exact pullback.condition
    have hhh : (ah≫pullback.fst q (f i))≫q=t≫f i := by
      rw [show ah≫pullback.fst q (f i)=p≫h from pullback.lift_fst _ _ _,Category.assoc,hh]
      exact pullback.condition
    have hag : ag≫baseFamily q (f i) ()=t := pullback.lift_snd _ _ _
    have K :
      pullHom ((F.map (pullback.fst q (f i)).op.toLoc).toFunctor.map a) ag
        (ag≫pullback.fst q (f i)) (ag≫pullback.fst q (f i)) ≫
        B.hom (i₁:=()) (i₂:=()) (t≫f i) (ag≫pullback.fst q (f i)) (ah≫pullback.fst q (f i)) hgg hhh =
      A.hom (i₁:=()) (i₂:=()) (t≫f i) (ag≫pullback.fst q (f i)) (ah≫pullback.fst q (f i)) hgg hhh ≫
        pullHom ((F.map (pullback.fst q (f i)).op.toLoc).toFunctor.map a) ah
          (ah≫pullback.fst q (f i)) (ah≫pullback.fst q (f i)) := by
      simpa [pullHom,mapComp'_eq_mapComp,Category.assoc,hag] using H'
    rw [pullHom_map,pullHom_map] at K
    have hk : t≫f i=p≫z := pullback.condition.symm
    have Kg : ag≫pullback.fst q (f i)=p≫g := pullback.lift_fst _ _ _
    have Kh : ah≫pullback.fst q (f i)=p≫h := pullback.lift_fst _ _ _
    refine ⟨ag≫pullback.fst q (f i),ah≫pullback.fst q (f i),Kg.symm,Kh.symm,?_⟩
    calc
      _ = pullHom ((F.map g.op.toLoc).toFunctor.map a) p
            (ag≫pullback.fst q (f i)) (ag≫pullback.fst q (f i)) Kg.symm Kg.symm ≫
          pullHom (B.hom z g h hg hh) p (ag≫pullback.fst q (f i)) (ah≫pullback.fst q (f i)) Kg.symm Kh.symm :=
        pullHom_comp_three F (M₁:=A.obj ()) (M₂:=B.obj ()) (M₃:=B.obj ())
          (f₁:=g) (f₂:=g) (f₃:=h) _ _ p _ _ _ Kg.symm Kg.symm Kh.symm
      _ = A.hom (i₁:=()) (i₂:=()) (t≫f i) (ag≫pullback.fst q (f i)) (ah≫pullback.fst q (f i)) hgg hhh ≫
          (F.map (ah≫pullback.fst q (f i)).op.toLoc).toFunctor.map a := by
        rw [pullHom_map,B.pullHom_hom (i₁:=()) (i₂:=()) p z (t≫f i) pullback.condition g h hg hh
          (ag≫pullback.fst q (f i)) (ah≫pullback.fst q (f i)) Kg.symm Kh.symm]
        exact K
      _ = pullHom (A.hom z g h hg hh) p (ag≫pullback.fst q (f i)) (ah≫pullback.fst q (f i)) Kg.symm Kh.symm ≫
          pullHom ((F.map h.op.toLoc).toFunctor.map a) p
            (ah≫pullback.fst q (f i)) (ah≫pullback.fst q (f i)) Kh.symm Kh.symm := by
        rw [A.pullHom_hom (i₁:=()) (i₂:=()) p z (t≫f i) pullback.condition g h hg hh
          (ag≫pullback.fst q (f i)) (ah≫pullback.fst q (f i)) Kg.symm Kh.symm,pullHom_map]
      _ = _ := (pullHom_comp_three F (M₁:=A.obj ()) (M₂:=A.obj ()) (M₃:=B.obj ())
        (f₁:=g) (f₂:=h) (f₃:=h) _ _ p _ _ _ Kg.symm Kh.symm Kh.symm).symm

/-- Prestack morphism descent constructs a genuine global comparison
isomorphism; its restriction is the prescribed actual cover isomorphism. -/
theorem exists_comparison_iso (M : F.obj (.mk (op Y)))
    (E : (F.toDescentData f).obj M ≅ localLiftsDatum F q P hPpull hff f D L hL e)
    (hpre : F.IsPrestackFor (Presieve.ofArrows _ (coverFamily q f))) :
    ∃ a : (F.map q.op.toLoc).toFunctor.obj M ≅ D.obj (),
      (F.toDescentData (coverFamily q f)).mapIso a =
        comparisonOnCover F q P hPpull hff f D L hL e M E := by
  let FF := (F.isPrestackFor_ofArrows_iff (coverFamily q f)).mp hpre |>.some
  refine ⟨FF.preimageIso (comparisonOnCover F q P hPpull hff f D L hL e M E),?_⟩
  apply Iso.ext
  exact FF.map_preimage _

/-- Stack effectiveness produces an actual global object with an actual
isomorphism to the constructed local F-descent datum. -/
theorem exists_global_lift (hStack : F.IsStackFor (Presieve.ofArrows U f)) :
    ∃ M : F.obj (.mk (op Y)), Nonempty ((F.toDescentData f).obj M ≅
      localLiftsDatum F q P hPpull hff f D L hL e) := by
  haveI : (F.toDescentData f).IsEquivalence := (F.isStackFor_ofArrows_iff f).mp hStack
  exact ⟨_,⟨(F.toDescentData f).objObjPreimageIso (localLiftsDatum F q P hPpull hff f D L hL e)⟩⟩

end LocalLifts
/-- Local effectiveness descends through a stack cover. The only chosen
objects are the supplied local lifts; both the global object and its genuine
q-descent-data isomorphism are constructed by stack and morphism descent. -/
theorem exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w,w'})
    (P : ∀ X : C,F.obj (.mk (op X)) → Prop)
    (hPpull : ∀ (X Z : C) (g : Z ⟶ X) (M : F.obj (.mk (op X))),
      P X M → P Z ((F.map g.op.toLoc).toFunctor.obj M))
    (hPiso : ∀ (X : C) (M N : F.obj (.mk (op X))), Nonempty (M≅N) → P X M → P X N)
    {Y' Y : C} (q : Y' ⟶ Y) {ι : Type t} {U : ι → C} (f : ∀ i,U i ⟶ Y)
    (hStack : F.IsStackFor (Presieve.ofArrows U f))
    (hpre : ∀ (Z : C) (z : Z ⟶ Y), F.IsPrestackFor (Presieve.ofArrows _ (coverFamily z f)))
    (hff : ∀ (Z : C) (z : Z ⟶ Y) (M N : F.obj (.mk (op Z))), P Z M → P Z N →
      Function.Bijective ((F.toDescentData (baseFamily q z)).map : (M ⟶ N) → _))
    (D : F.DescentData (fun _ : Unit => q))
    (hlocal : ∀ i,∃ L : F.obj (.mk (op (U i))), P (U i) L ∧
      Nonempty ((F.toDescentData (baseFamily q (f i))).obj L ≅ (basePull F q (f i)).obj D)) :
    ∃ M : F.obj (.mk (op Y)), (∀ i,P (U i) ((F.map (f i).op.toLoc).toFunctor.obj M)) ∧
      Nonempty ((F.toDescentData (fun _ : Unit => q)).obj M ≅ D) := by
  classical
  choose L hL e using hlocal
  let e' := fun i => (e i).some
  obtain ⟨M,⟨E⟩⟩ := exists_global_lift F q P hPpull hff f D L hL e' hStack
  obtain ⟨a,ha⟩ := exists_comparison_iso F q P hPpull hff f D L hL e' M E (hpre Y' q)
  let si := localGlobalIso F q P hPpull hff f D L hL e' M E
  let H := homOfLocalCompatibility F q f hpre ((F.toDescentData (fun _ : Unit => q)).obj M) D a.hom
    (fun i => (si i).hom) (fun i => (comparison_local_component F q P hPpull hff f D L hL e' M E a ha i).symm)
  refine ⟨M,?_,⟨isoMk (fun _ : Unit => a) ?_⟩⟩
  · intro i
    exact hPiso (U i) (L i) _ ⟨((evaluate F f i).mapIso E).symm⟩ (hL i)
  · intro Z z i j g h hg hh
    cases i
    cases j
    exact H.comm (i₁:=()) (i₂:=()) z g h hg hh

#print axioms exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj
#print axioms homOfLocalCompatibility
#print axioms exists_comparison_iso
#print axioms localEffectivityIso
#print axioms localLiftsDatum
#print axioms exists_global_lift
#print axioms overlapHom_self
#print axioms overlapHom_comp
end CategoryTheory.Pseudofunctor.DescentData
