import ThetaCoverClassPortable.KummerSquareLine

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle
namespace FourCorner.KummerTrivialLine
variable {X : Scheme} [IsIntegral X] {ι : Type} {U : ι → X.Opens}
    (cc : UnitCocycle U) (e : glueOfCocycle cc ≅ 𝟙_ X.Modules)

def frameImage (i : ι) : Γ(X,U i) := e.hom.app (U i) (glueFrame cc i)

lemma frameImage_isUnit (i : ι) : IsUnit (frameImage cc e i) := by
  have hb := (isFrameOn_glueFrame cc i).map_iso e
  have hsur := (hb (le_refl (U i)) (le_refl (U i))).surjective
  obtain ⟨b,hb⟩ := hsur (unitSection (U i))
  have hr : (𝟙_ X.Modules).presheaf.map (homOfLE (le_refl (U i))).op
      (e.hom.app (U i) (glueFrame cc i))=e.hom.app (U i) (glueFrame cc i) := by
    rw [Subsingleton.elim (homOfLE (le_refl (U i))) (𝟙 (U i)),op_id,(𝟙_ X.Modules).presheaf.map_id]
    rfl
  rw [hr] at hb
  change b*frameImage cc e i=1 at hb
  exact IsUnit.of_mul_eq_one b (by rwa [mul_comm])

def imageUnit (i : ι) : Γ(X,U i)ˣ := (frameImage_isUnit cc e i).unit

lemma imageUnit_value (i : ι) : (imageUnit cc e i:Γ(X,U i))=frameImage cc e i := IsUnit.unit_spec _

lemma frameImage_transition (i j : ι) :
    rO (inf_le_right : U i ⊓ U j ≤ U j) (frameImage cc e j)=
      cc.u i j * rO inf_le_left (frameImage cc e i) := by
  have hn {V W : X.Opens} (h : W≤V) (s : Γ(glueOfCocycle cc,V)) :
      (𝟙_ X.Modules).presheaf.map (homOfLE h).op (e.hom.app V s)=
        e.hom.app W ((glueOfCocycle cc).presheaf.map (homOfLE h).op s) := by
    have hh := e.hom.mapPresheaf.naturality (homOfLE h).op
    exact (congrFun (congrArg (fun f=> (ConcreteCategory.hom f : Γ(glueOfCocycle cc,V)→Γ(𝟙_ X.Modules,W))) hh) s).symm
  change (𝟙_ X.Modules).presheaf.map (homOfLE inf_le_right).op (e.hom.app (U j) (glueFrame cc j)) = _
  rw [hn,map_glueFrame_eq_smul,Scheme.Modules.Hom.app_smul,←hn]
  rfl

section Field
variable [∀i,Nonempty (U i)] (q : ι → X.functionField)
    (hq : ∀i,q i≠0)
    (hc : ∀i j,
      letI : Nonempty ((U i ⊓ U j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
      algebraMap Γ(X,U i ⊓ U j) X.functionField (cc.u i j)=q j/q i)
local instance pair_nonempty (i j : ι) : Nonempty ((U i ⊓ U j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _

include hq hc in
theorem quotient_independent (i j : ι) :
    q i/algebraMap Γ(X,U i) X.functionField (imageUnit cc e i:Γ(X,U i))=
      q j/algebraMap Γ(X,U j) X.functionField (imageUnit cc e j:Γ(X,U j)) := by
  have htrans := congrArg (algebraMap Γ(X,U i ⊓ U j) X.functionField) (frameImage_transition cc e i j)
  rw [map_mul,KummerUnitCocycle.germ_res,KummerUnitCocycle.germ_res,hc i j] at htrans
  have hi : algebraMap Γ(X,U i) X.functionField (imageUnit cc e i:Γ(X,U i))≠0 :=
    ((imageUnit cc e i).isUnit.map _).ne_zero
  have hj : algebraMap Γ(X,U j) X.functionField (imageUnit cc e j:Γ(X,U j))≠0 :=
    ((imageUnit cc e j).isUnit.map _).ne_zero
  simp only [←imageUnit_value] at htrans
  field_simp [hi,hj,hq i] at htrans ⊢
  exact htrans

/- An actual trivialization produces one native rational function whose
local quotients are actual regular units. This is the effective direction
needed to prove principal divisors, rather than an assumed Pic comparison. -/
include hq hc in
theorem trivial_yields_principal_data [Nonempty ι] :
    ∃f : X.functionField,f≠0 ∧ ∀i,
      f=q i/algebraMap Γ(X,U i) X.functionField (imageUnit cc e i:Γ(X,U i)) := by
  let i : ι := Classical.choice inferInstance
  refine ⟨q i/algebraMap Γ(X,U i) X.functionField (imageUnit cc e i:Γ(X,U i)),?_,fun j=>quotient_independent cc e q hq hc i j⟩
  exact div_ne_zero (hq i) (((imageUnit cc e i).isUnit.map _).ne_zero)
end Field
#print axioms trivial_yields_principal_data
end FourCorner.KummerTrivialLine
