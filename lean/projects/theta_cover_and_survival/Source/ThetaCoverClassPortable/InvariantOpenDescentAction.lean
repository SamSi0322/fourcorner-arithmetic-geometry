import ThetaCoverClassPortable.DescentActionAlongMono
import ThetaCoverClassPortable.GeneralAffineDescentQuotient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FourCorner.InvariantOpenDescentAction
variable {S S' X : Scheme.{u}} (s:S'⟶S) (x:X⟶S') (𝒜:DescentAction s x)
  (W:X.Opens) (hW:pullback.fst (x≫s) s ⁻¹ᵁ W=𝒜.act ⁻¹ᵁ W)
abbrev r := DescentActionAlongMono.relMap s x W.ι

include hW in
lemma range_action : Set.range (r s x W≫𝒜.act) ⊆ Set.range W.ι := by
  rintro _ ⟨z,rfl⟩
  rw [Scheme.Opens.range_ι]
  have hz : r s x W z ∈ pullback.fst (x≫s) s ⁻¹ᵁ W := by
    change pullback.fst (x≫s) s (r s x W z)∈W
    rw [←Scheme.Hom.comp_apply,DescentActionAlongMono.relMap_fst,Scheme.Hom.comp_apply]
    exact (pullback.fst ((W.ι≫x)≫s) s z).property
  rw [hW] at hz
  exact hz

def act : pullback ((W.ι≫x)≫s) s ⟶ W :=
  IsOpenImmersion.lift W.ι (r s x W≫𝒜.act) (range_action s x 𝒜 W hW)
@[reassoc (attr:=simp)] lemma act_ι : act s x 𝒜 W hW≫W.ι=r s x W≫𝒜.act :=
  IsOpenImmersion.lift_fac _ _ _

def action : DescentAction s (W.ι≫x) :=
  DescentActionAlongMono.ofMap s x W.ι 𝒜 (act s x 𝒜 W hW) (act_ι s x 𝒜 W hW)

/-- The relation on the open is its TRUE pullback relation, not an abstract
replacement pair. -/
lemma rel_cartesian : IsPullback (r s x W) (pullback.fst ((W.ι≫x)≫s) s)
    (pullback.fst (x≫s) s) W.ι := by
  have ho := (IsPullback.of_hasPullback ((W.ι≫x)≫s) s).flip
  have outer : IsPullback (r s x W≫pullback.snd (x≫s) s)
      (pullback.fst ((W.ι≫x)≫s) s) s (W.ι≫(x≫s)) := by
    simpa only [r,DescentActionAlongMono.relMap_snd,Category.assoc] using ho
  exact outer.of_right (DescentActionAlongMono.relMap_fst s x W.ι)
    (IsPullback.of_hasPullback (x≫s) s).flip

def relationIso : pullback ((W.ι≫x)≫s) s ≅
    ((pullback.fst (x≫s) s ⁻¹ᵁ W) : Scheme.{u}) :=
  (rel_cartesian s x W).isoPullback ≪≫
    ((isPullback_morphismRestrict (pullback.fst (x≫s) s) W).flip).isoPullback.symm

@[reassoc (attr:=simp)] lemma relationIso_ι :
    (relationIso s x W).hom≫(pullback.fst (x≫s) s ⁻¹ᵁ W).ι=r s x W := by
  simp [relationIso,Category.assoc]
@[reassoc (attr:=simp)] lemma relationIso_fst :
    (relationIso s x W).hom≫(pullback.fst (x≫s) s ∣_ W)=pullback.fst ((W.ι≫x)≫s) s := by
  simp [relationIso,Category.assoc]

def tRes : ((pullback.fst (x≫s) s ⁻¹ᵁ W) : Scheme.{u}) ⟶ W :=
  ((pullback (x≫s) s).isoOfEq hW).hom≫(𝒜.act ∣_ W)
@[reassoc (attr:=simp)] lemma tRes_ι : tRes s x 𝒜 W hW≫W.ι=
    (pullback.fst (x≫s) s ⁻¹ᵁ W).ι≫𝒜.act := by
  simp [tRes,Category.assoc]
@[reassoc (attr:=simp)] lemma relationIso_act :
    (relationIso s x W).hom≫tRes s x 𝒜 W hW=(action s x 𝒜 W hW).act := by
  apply (cancel_mono W.ι).mp
  simp only [Category.assoc,tRes_ι,relationIso_ι_assoc]
  exact (act_ι s x 𝒜 W hW).symm
end FourCorner.InvariantOpenDescentAction
