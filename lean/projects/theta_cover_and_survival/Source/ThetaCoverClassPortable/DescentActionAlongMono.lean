import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_DescentAction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FourCorner.DescentActionAlongMono
variable {S S' X X' : Scheme.{u}} (s:S'⟶S) (x:X⟶S') (j:X'⟶X)

def relMap : pullback ((j≫x)≫s) s ⟶ pullback (x≫s) s :=
  pullback.map ((j≫x)≫s) s (x≫s) s j (𝟙 _) (𝟙 _)
    (by simp [Category.assoc]) (by simp)
@[reassoc (attr:=simp)] lemma relMap_fst : relMap s x j ≫ pullback.fst _ _=pullback.fst _ _≫j :=
  pullback.lift_fst _ _ _
@[reassoc (attr:=simp)] lemma relMap_snd : relMap s x j ≫ pullback.snd _ _=pullback.snd _ _ := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
instance relMap_isIso [IsIso j] : IsIso (relMap s x j) := by dsimp [relMap];infer_instance

def tripleMap : pullback (pullback.snd ((j≫x)≫s) s ≫ s) s ⟶
    pullback (pullback.snd (x≫s) s ≫ s) s :=
  pullback.map _ _ _ _ (relMap s x j) (𝟙 _) (𝟙 _)
    (by simp [Category.assoc]) (by simp)
@[reassoc (attr:=simp)] lemma tripleMap_fst : tripleMap s x j ≫ pullback.fst _ _=
    pullback.fst _ _≫relMap s x j := pullback.lift_fst _ _ _
@[reassoc (attr:=simp)] lemma tripleMap_snd : tripleMap s x j ≫ pullback.snd _ _=pullback.snd _ _ := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma unitMap_relMap : DescentAction.unitMap s (j≫x) ≫ relMap s x j=
    j≫DescentAction.unitMap s x := by
  apply pullback.hom_ext <;> simp [Category.assoc]
lemma proj13_relMap : DescentAction.proj₁₃ s (j≫x) ≫ relMap s x j=
    tripleMap s x j ≫ DescentAction.proj₁₃ s x := by
  apply pullback.hom_ext <;> simp [Category.assoc]

variable (𝒜 : DescentAction s x)
  (a : pullback ((j≫x)≫s) s ⟶ X') (ha : a≫j=relMap s x j≫𝒜.act)
include ha
lemma act_comp : a≫(j≫x)=pullback.snd _ _ := by
  calc a≫(j≫x)=(a≫j)≫x := (Category.assoc _ _ _).symm
    _ = (relMap s x j≫𝒜.act)≫x := congrArg (fun f=>f≫x) ha
    _ = relMap s x j≫pullback.snd (x≫s) s := by simp only [Category.assoc,𝒜.act_comp]
    _ = pullback.snd ((j≫x)≫s) s := relMap_snd s x j
lemma actMap_relMap : DescentAction.actMap a (act_comp s x j 𝒜 a ha) ≫ relMap s x j=
    tripleMap s x j ≫ DescentAction.actMap 𝒜.act 𝒜.act_comp := by
  apply pullback.hom_ext <;> simp [Category.assoc,ha]

/-- Inherit the actual action axioms along a mono from a specified ACTUAL
map lifting the action. No unit/cocycle/effectivity conclusion is assumed. -/
def ofMap [Mono j] : DescentAction s (j≫x) where
  act := a
  act_comp := act_comp s x j 𝒜 a ha
  unit_act := by
    apply (cancel_mono j).mp
    calc (DescentAction.unitMap s (j≫x)≫a)≫j=
        (DescentAction.unitMap s (j≫x)≫relMap s x j)≫𝒜.act := by simp only [Category.assoc,ha]
      _ = j := by rw [unitMap_relMap,Category.assoc,𝒜.unit_act,Category.comp_id]
      _ = 𝟙 X'≫j := (Category.id_comp _).symm
  trans := by
    apply (cancel_mono j).mp
    calc (DescentAction.actMap a (act_comp s x j 𝒜 a ha)≫a)≫j=
        (DescentAction.actMap a (act_comp s x j 𝒜 a ha)≫relMap s x j)≫𝒜.act := by
          simp only [Category.assoc,ha]
      _ = (tripleMap s x j≫DescentAction.actMap 𝒜.act 𝒜.act_comp)≫𝒜.act := by rw [actMap_relMap s x j 𝒜 a ha]
      _ = (tripleMap s x j≫DescentAction.proj₁₃ s x)≫𝒜.act := by
          simpa only [Category.assoc] using congrArg (fun f=>tripleMap s x j≫f) 𝒜.trans
      _ = (DescentAction.proj₁₃ s (j≫x)≫relMap s x j)≫𝒜.act := by rw [proj13_relMap]
      _ = (DescentAction.proj₁₃ s (j≫x)≫a)≫j := by simp only [Category.assoc,ha]
end FourCorner.DescentActionAlongMono
