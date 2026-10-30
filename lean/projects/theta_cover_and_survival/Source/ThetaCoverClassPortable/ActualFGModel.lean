import ThetaCoverClassPortable.FixedCurveStageGeometry
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import ThetaCoverClassPortable.RigidificationCompensation
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_AffineLimit

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.Scheme.TwoAffineOpenCover NeronModelInfra
namespace FourCorner.ActualFGModel

variable (R : Type u) [CommRing R] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) [QuasiCompact c] [QuasiSeparated c]

/-- An actual invertible sheaf on the base changed fixed curve descends to an actual
finitely generated subalgebra. No stage sheaf or stage existence is supplied. -/
theorem exists_invertible_fg_model
    (A : Type u) [CommRing A] [Algebra R A]
    (M : (pullback c (specMap R A)).Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ (D : Subalgebra R A), D.FG ∧
      ∃ (M0 : (pullback c (specMap R ↥D)).Modules), Scheme.Modules.IsInvertible M0 ∧
        Nonempty ((Scheme.Modules.pullback (baseChangeSnd c (stageHom R D.val))).obj M0 ≅ M) := by
  classical
  let i := firstStage R A
  let f0 := pullback.snd c (specMap R (stageRing R A i))
  have hA := AlgebraicGeometry.RelPicard.isPullback_baseChangeSnd c (stageHom R i.1.val)
  let eA := hA.isoPullback
  let N := (Scheme.Modules.pullback eA.inv).obj M
  obtain ⟨k,hik,Nk,hNk,H⟩ :=
    Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
      (transition R A) (into R A) (stage_isDirectLimit R A) i f0 N (hM.pullback eA.inv)
  have hk := AlgebraicGeometry.RelPicard.isPullback_baseChangeSnd c
    (stageHom R (Subalgebra.inclusion (show i.1 ≤ k.1 from hik)))
  let ek := hk.isoPullback
  let σ := baseChangeSnd c (stageHom R k.1.val)
  let M0 := (Scheme.Modules.pullback ek.hom).obj Nk
  let cmp := eA.inv ≫ σ ≫ ek.hom
  have hc1 : cmp ≫ pullback.fst f0 (Spec.map (CommRingCat.ofHom (transition R A i k hik))) =
      pullback.fst f0 (Spec.map (CommRingCat.ofHom (into R A i))) := by
    change (hA.isoPullback.inv ≫ baseChangeSnd c (stageHom R k.1.val) ≫ hk.isoPullback.hom) ≫
        pullback.fst (pullback.snd c (specMap R ↥i.1))
          (stageHom R (Subalgebra.inclusion (show i.1 ≤ k.1 from hik))).1 =
      pullback.fst (pullback.snd c (specMap R ↥i.1)) (stageHom R i.1.val).1
    simp only [Category.assoc,hk.isoPullback_hom_fst]
    rw [baseChange_stage_comp R c i k hik,hA.isoPullback_inv_fst]
  have hσsnd : σ ≫ pullback.snd c (specMap R (stageRing R A k)) =
      pullback.snd c (specMap R A) ≫ Spec.map (CommRingCat.ofHom (into R A k)) :=
    pullback.lift_snd _ _ _
  have hc2 : cmp ≫ pullback.snd f0 (Spec.map (CommRingCat.ofHom (transition R A i k hik))) =
      pullback.snd f0 (Spec.map (CommRingCat.ofHom (into R A i))) ≫
        Spec.map (CommRingCat.ofHom (into R A k)) := by
    change (hA.isoPullback.inv ≫ σ ≫ hk.isoPullback.hom) ≫
        pullback.snd (pullback.snd c (specMap R ↥i.1))
          (stageHom R (Subalgebra.inclusion (show i.1 ≤ k.1 from hik))).1 =
      pullback.snd (pullback.snd c (specMap R ↥i.1)) (stageHom R i.1.val).1 ≫
        Spec.map (CommRingCat.ofHom (into R A k))
    simp only [Category.assoc,hk.isoPullback_hom_snd]
    erw [hσsnd,← Category.assoc,hA.isoPullback_inv_snd]
  obtain ⟨eN⟩ := H cmp hc1 hc2
  have hcmp : σ ≫ ek.hom = eA.hom ≫ cmp := by
    simp [cmp,Category.assoc]
  refine ⟨k.1,k.2,M0,hNk.pullback ek.hom,⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp σ ek.hom).app Nk ≪≫
    (Scheme.Modules.pullbackCongr hcmp).app Nk ≪≫
    ((Scheme.Modules.pullbackComp eA.hom cmp).app Nk).symm ≪≫
    (Scheme.Modules.pullback eA.hom).mapIso eN ≪≫
    (Scheme.Modules.pullbackComp eA.hom eA.inv).app M ≪≫
    (Scheme.Modules.pullbackCongr eA.hom_inv_id).app M ≪≫
    (Scheme.Modules.pullbackId _).app M

/-- Rigidification is constructed at the finite stage and compared after actual base change.
The input rigidification is a Nonempty trivialization, not a selected frame. -/
theorem exists_rigidified_fg_model
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A]
    (L : RigidifiedLineBundle c ε (specMap R A)) :
    ∃ (D : Subalgebra R A), D.FG ∧
      ∃ (L0 : RigidifiedLineBundle c ε (specMap R ↥D)),
        Nonempty ((L0.pullbackAlong (stageHom R D.val)).L ≅ L.L) := by
  obtain ⟨D,hD,M0,hM0,⟨eM⟩⟩ := exists_invertible_fg_model R c A L.L L.isInvertible
  let L0 := RigidifiedLineBundle.ofInvertible (ε:=ε) M0 hM0
  refine ⟨D,hD,L0,⟨?_⟩⟩
  exact (RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (stageHom R D.val) hM0).some ≪≫
    Scheme.Modules.rigidifyMapIso _ _ eM ≪≫
    FourCorner.RigidificationCompensation.rigidifyCounitIso _ _ L.rigidified.some

/-- Finite-stage surjectivity of the actual raw relative Picard functor on all test algebras. -/
theorem isLFPSurj_relPicardPresheaf
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    AffineLimit.IsLFPSurj (relPicardPresheaf c ε) := by
  intro A _ _ x
  induction x using Quotient.inductionOn with
  | h L =>
    obtain ⟨D,hD,L0,he⟩ := exists_rigidified_fg_model R c ε A L
    exact ⟨D,hD,Quotient.mk _ L0,Quotient.sound he⟩

end FourCorner.ActualFGModel
