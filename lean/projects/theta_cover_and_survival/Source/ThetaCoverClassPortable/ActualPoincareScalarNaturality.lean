import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import ThetaCoverClassPortable.ActualDictionaryClassCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.RelPicard.BaseChange AlgebraicGeometry.SmoothProperCurve
universe u
namespace FourCorner.ActualGeometricCoverDeltaComparison

/-- The actual inverse to the first projection from pullback along identity,
valid over every commutative base ring. -/
def identityPullbackLift {R : Type u} [CommRing R] {X : Scheme.{u}} (x : X ⟶ Spec (.of R)) :
    X ⟶ pullback x (𝟙 (Spec (.of R))) := pullback.lift (𝟙 X) x (by simp)

@[reassoc] theorem identityPullbackLift_fst {R : Type u} [CommRing R] {X : Scheme.{u}} (x : X ⟶ Spec (.of R)) :
    identityPullbackLift x ≫ pullback.fst x (𝟙 _)=𝟙 X := pullback.lift_fst _ _ _

@[reassoc] theorem identityPullbackLift_snd {R : Type u} [CommRing R] {X : Scheme.{u}} (x : X ⟶ Spec (.of R)) :
    identityPullbackLift x ≫ pullback.snd x (𝟙 _)=x := pullback.lift_snd _ _ _

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (D : RelativePic0Designation R c) (S : Type u) [CommRing S] [Algebra R S]

/-- Literal pullback of a specified point; both projections are fixed. -/
def scalarPoint (p : SchemeHomOver (𝟙 (Spec (.of R))) D.toBase) :
    SchemeHomOver (𝟙 (Spec (.of S))) (D.baseChange S).toBase :=
  ⟨pullback.lift (specMap R S ≫ p.val) (𝟙 _) (by rw [Category.assoc,p.property,Category.comp_id,Category.id_comp]),
    pullback.lift_snd _ _ _⟩

lemma scalarPoint_fst (p : SchemeHomOver (𝟙 (Spec (.of R))) D.toBase) :
    (scalarPoint c D S p).val ≫ pullback.fst D.toBase (specMap R S)=specMap R S ≫ p.val :=
  pullback.lift_fst _ _ _

private def collapseThree {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Y) (d : Y ⟶ Z)
    (L : Z.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback d).obj L)) ≅
      (Scheme.Modules.pullback (a ≫ (b ≫ d))).obj L :=
  (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.pullbackComp b d).app L) ≪≫
    (Scheme.Modules.pullbackComp a (b ≫ d)).app L

/-- Scalar extension preserves the actual Poincare fibre of the specified
point, and identifies it with the actual pullback of the original line.
The representation over S is any genuine base-change representation with
its explicit Poincare comparison; no target class or point equality is assumed. -/
theorem scalarPoint_poincare_line
    (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (p : SchemeHomOver (𝟙 (Spec (.of R))) D.toBase)
    (L : C.Modules)
    (hL : Nonempty ((h.poincare.pullbackAlong p).L ≅
      (Scheme.Modules.pullback (pullback.fst c (𝟙 (Spec (.of R))))).obj L))
    (hS : RepresentsRelSubPic (baseChange R c S) (sectionBaseChange S ε)
      (algEquivZeroCut (baseChange R c S) (sectionBaseChange S ε)) (D.baseChange S))
    (hP : Nonempty (hS.poincare.L ≅ (BaseChange.ofR c ε S
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R S),pullback.condition⟩)).L)) :
    Nonempty ((Scheme.Modules.pullback (identityPullbackLift (baseChange R c S))).obj
      (hS.poincare.pullbackAlong (scalarPoint c D S p)).L ≅
      (Scheme.Modules.pullback (pullback.fst c (specMap R S))).obj L) := by
  let a := identityPullbackLift (baseChange R c S)
  let b := baseChangeSnd (baseChange R c S) (scalarPoint c D S p)
  let q : SchemeHomOver ((D.baseChange S).toBase ≫ specMap R S) D.toBase :=
    ⟨pullback.fst D.toBase (specMap R S),pullback.condition⟩
  let d := baseChangeSnd c q
  let t := (κ c S (D.baseChange S).toBase).hom
  let r := pullback.fst c (specMap R S)
  have heq : a ≫ (b ≫ (t ≫ d))=r ≫ (identityPullbackLift c ≫ baseChangeSnd c p) := by
    apply pullback.hom_ext <;>
      simp [a,b,t,d,r,q,κ,baseChangeSnd,identityPullbackLift,scalarPoint,Category.assoc,Category.id_comp]
    · exact Category.id_comp _
    · simpa only [Category.assoc] using congrArg (· ≫ p.val) (pullback.condition (f:=c) (g:=specMap R S)).symm
  obtain ⟨eP⟩ := hP
  obtain ⟨eL⟩ := hL
  have first : (Scheme.Modules.pullback a).obj (hS.poincare.pullbackAlong (scalarPoint c D S p)).L ≅
      (Scheme.Modules.pullback (a ≫ (b ≫ (t ≫ d)))).obj h.poincare.L :=
    (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.pullback b).mapIso eP) ≪≫
      (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.pullback b).mapIso
        ((Scheme.Modules.pullbackComp t d).app h.poincare.L)) ≪≫
      (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.pullbackComp b (t ≫ d)).app h.poincare.L) ≪≫
      (Scheme.Modules.pullbackComp a (b ≫ (t ≫ d))).app h.poincare.L
  refine ⟨first ≪≫ (Scheme.Modules.pullbackCongr heq).app h.poincare.L ≪≫
    (collapseThree r (identityPullbackLift c) (baseChangeSnd c p) h.poincare.L).symm ≪≫
    (Scheme.Modules.pullback r).mapIso ((Scheme.Modules.pullback (identityPullbackLift c)).mapIso eL) ≪≫
    collapseThree r (identityPullbackLift c) (pullback.fst c (𝟙 _)) L ≪≫
    (Scheme.Modules.pullbackCongr (by rw [identityPullbackLift_fst,Category.comp_id])).app L⟩

end FourCorner.ActualGeometricCoverDeltaComparison
