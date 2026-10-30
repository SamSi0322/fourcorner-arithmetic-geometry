import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.RigidifiedFFIsoCoherence
import ThetaCoverClassPortable.DescentDataPrimeComputation
import ThetaCoverClassPortable.DescentDataPrimeIsoLifting
import ThetaCoverClassPortable.DescentFunctorCoherence
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry"



noncomputable section
namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pseudofunctor Surjective Scheme.Modules.pullback Scheme.Pullback.range_fst Spec Scheme Flat Scheme.Modules.pullbackCongr flat_and_surjective_SpecMap_iff Scheme.Modules IsAffineHom Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RigidifiedLineBundle Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp baseChangeSnd_comp rigSection_baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq"
namespace DescentAux
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

open NeronModelInfra

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

lemma isPullback_baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by
  have big : IsPullback (baseChangeSnd c ψ ≫ pullback.fst c t) (pullback.snd c t') c (ψ.1 ≫ t) := by
    rw [ψ.2, show baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' from
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)]
    exact IsPullback.of_hasPullback c t'
  exact big.of_right ((pullback.lift_snd _ _ _)) (IsPullback.of_hasPullback c t)

lemma isPullback_baseChangeSnd {X U V W : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of R)}
    {uS : U ⟶ Spec (CommRingCat.of R)} {vS : V ⟶ Spec (CommRingCat.of R)} {wS : W ⟶ Spec (CommRingCat.of R)}
    (u : SchemeHomOver uS x) (v : SchemeHomOver vS x) (a : SchemeHomOver wS uS) (b : SchemeHomOver wS vS)
    (h : IsPullback a.1 b.1 u.1 v.1) :
    IsPullback (baseChangeSnd c a) (baseChangeSnd c b) (baseChangeSnd c u) (baseChangeSnd c v) := by
  have hbig : IsPullback (pullback.snd c wS ≫ a.1) (baseChangeSnd c b) u.1 (pullback.snd c vS ≫ v.1) :=
    (isPullback_baseChangeSnd_snd c b).flip.paste_horiz h
  have hbig' : IsPullback (baseChangeSnd c a ≫ pullback.snd c uS) (baseChangeSnd c b) u.1
      (baseChangeSnd c v ≫ pullback.snd c x) := by
    rw [show baseChangeSnd c a ≫ pullback.snd c uS = pullback.snd c wS ≫ a.1 from pullback.lift_snd _ _ _,
      show baseChangeSnd c v ≫ pullback.snd c x = pullback.snd c vS ≫ v.1 from pullback.lift_snd _ _ _]
    exact hbig
  refine hbig'.of_right ?_ (isPullback_baseChangeSnd_snd c u).flip
  rw [baseChangeSnd_comp, baseChangeSnd_comp]
  congr 1
  exact Subtype.ext h.w

abbrev strMap₁₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    pullback ψ₁.1 ψ₂.1 ⟶ Spec (CommRingCat.of R) :=
  pullback.fst ψ₁.1 ψ₂.1 ≫ t₁

def pr₁ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₁ :=
  ⟨pullback.fst ψ₁.1 ψ₂.1, rfl⟩

def pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₂ :=
  ⟨pullback.snd ψ₁.1 ψ₂.1, by
    have h2 : pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1 ≫ t = pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ := by rw [ψ₂.2]
    have h1 : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 ≫ t = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁ := by rw [ψ₁.2]
    change pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁
    rw [← h2, ← h1, ← Category.assoc, ← pullback.condition, Category.assoc]⟩

@[scoped simp] lemma pr₁_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₁ ψ₁ ψ₂).1 = pullback.fst ψ₁.1 ψ₂.1 := rfl

@[scoped simp] lemma pr₂_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₂ ψ₁ ψ₂).1 = pullback.snd ψ₁.1 ψ₂.1 := rfl

lemma postComp_pr₁_eq_postComp_pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    postComp ψ₁ (pr₁ ψ₁ ψ₂) = postComp ψ₂ (pr₂ ψ₁ ψ₂) :=
  Subtype.ext pullback.condition

def chosenPullback {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    ChosenPullback (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) where
  pullback := Limits.pullback c (strMap₁₂ ψ₁ ψ₂)
  p₁ := baseChangeSnd c (pr₁ ψ₁ ψ₂)
  p₂ := baseChangeSnd c (pr₂ ψ₁ ψ₂)
  condition := by
    rw [baseChangeSnd_comp, baseChangeSnd_comp, postComp_pr₁_eq_postComp_pr₂]
  isLimit := (isPullback_baseChangeSnd c ψ₁ ψ₂ (pr₁ ψ₁ ψ₂) (pr₂ ψ₁ ψ₂)
    (IsPullback.of_hasPullback ψ₁.1 ψ₂.1)).isLimit
  p := baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂))
  hp₁ := baseChangeSnd_comp c _ _

@[scoped simp] lemma chosenPullback_p₁ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (chosenPullback c ψ₁ ψ₂).p₁ = baseChangeSnd c (pr₁ ψ₁ ψ₂) := rfl

@[scoped simp] lemma chosenPullback_p₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (chosenPullback c ψ₁ ψ₂).p₂ = baseChangeSnd c (pr₂ ψ₁ ψ₂) := rfl

def chosenPullback₃ {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    ChosenPullback₃ (chosenPullback c ψ ψ) (chosenPullback c ψ ψ) (chosenPullback c ψ ψ) where
  chosenPullback := chosenPullback c (pr₂ ψ ψ) (pr₁ ψ ψ)
  p := baseChangeSnd c (postComp (postComp ψ (pr₁ ψ ψ)) (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  p₁ := baseChangeSnd c (postComp (pr₁ ψ ψ) (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  p₃ := baseChangeSnd c (postComp (pr₂ ψ ψ) (pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)))
  l :=
    { f := baseChangeSnd c
        ⟨pullback.lift ((pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)).1 ≫ (pr₁ ψ ψ).1) ((pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)).1 ≫ (pr₂ ψ ψ).1)
          (by
            have hT₂ : pullback.fst ψ.1 ψ.1 ≫ ψ.1 = pullback.snd ψ.1 ψ.1 ≫ ψ.1 := pullback.condition
            have hT₃ : pullback.fst (pullback.snd ψ.1 ψ.1) (pullback.fst ψ.1 ψ.1) ≫ pullback.snd ψ.1 ψ.1 =
                pullback.snd (pullback.snd ψ.1 ψ.1) (pullback.fst ψ.1 ψ.1) ≫ pullback.fst ψ.1 ψ.1 :=
              pullback.condition
            simp only [pr₁_val, pr₂_val, Category.assoc]
            rw [hT₂, ← Category.assoc, hT₃, Category.assoc, hT₂]),
         by
          simp only [pr₁_val, pr₂_val]
          rw [← Category.assoc, pullback.lift_fst, Category.assoc]
          rfl⟩
      f_p₁ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₁ ψ ψ) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_fst _ _ _)
      f_p₂ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₂ ψ ψ) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_snd _ _ _)
      f_p := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (postComp ψ (pr₁ ψ ψ)) = _
        erw [baseChangeSnd_comp]; congr 1
        exact Subtype.ext (by
          change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ ψ.1 = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ ψ.1
          rw [pullback.lift_fst_assoc, Category.assoc]
          rfl) }
  hp₁ := by
    change baseChangeSnd c (pr₁ (pr₂ ψ ψ) (pr₁ ψ ψ)) ≫ baseChangeSnd c (pr₁ ψ ψ) = _
    erw [baseChangeSnd_comp]
  hp₃ := by
    change baseChangeSnd c (pr₂ (pr₂ ψ ψ) (pr₁ ψ ψ)) ≫ baseChangeSnd c (pr₂ ψ ψ) = _
    erw [baseChangeSnd_comp]

end AlgebraicGeometry.RelPicard.DescentAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry"
end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux"

noncomputable section
namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pseudofunctor Surjective Scheme.Modules.pullback Scheme.Pullback.range_fst Spec Scheme Flat Scheme.Modules.pullbackCongr flat_and_surjective_SpecMap_iff Scheme.Modules IsAffineHom Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RigidifiedLineBundle Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp baseChangeSnd_comp rigSection_baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq"
namespace DescentAux
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "NeronModelInfra AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.Scheme.Modules"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

structure RigData {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) where
  L : (Limits.pullback c t).Modules
  isInvertible : Scheme.Modules.IsInvertible L
  α : (Scheme.Modules.pullback (rigSection c t ε)).obj L ≅ SheafOfModules.unit T.ringCatSheaf

namespace RigData

variable {c ε} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

def Compat (A B : RigData c ε t) (φ : A.L ⟶ B.L) : Prop :=
  (Scheme.Modules.pullback (rigSection c t ε)).map φ ≫ B.α.hom = A.α.hom

lemma Compat.id (A : RigData c ε t) : Compat A A (𝟙 A.L) := by
  simp [Compat]

lemma Compat.comp {A B D : RigData c ε t} {φ : A.L ⟶ B.L} {ψ : B.L ⟶ D.L} (hφ : Compat A B φ)
    (hψ : Compat B D ψ) : Compat A D (φ ≫ ψ) := by
  simp only [Compat, Functor.map_comp, Category.assoc] at *
  rw [hψ, hφ]

lemma compat_iff_mapIso (A B : RigData c ε t) (φ : A.L ≅ B.L) :
    Compat A B φ.hom ↔ (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ ≪≫ B.α = A.α := by
  constructor
  · intro h; ext : 1; first | exact h | simpa using h | simpa [Compat] using h
  · intro h; first | exact congrArg Iso.hom h | simpa using congrArg Iso.hom h | simpa [Compat] using congrArg Iso.hom h

lemma Compat.inv {A B : RigData c ε t} {φ : A.L ≅ B.L} (h : Compat A B φ.hom) : Compat B A φ.inv := by
  simp only [Compat] at *
  rw [← h, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

def ofIso (A : RigData c ε t) (L' : (Limits.pullback c t).Modules) (e : L' ≅ A.L)
    (hL' : Scheme.Modules.IsInvertible L') : RigData c ε t where
  L := L'
  isInvertible := hL'
  α := (Scheme.Modules.pullback (rigSection c t ε)).mapIso e ≪≫ A.α

lemma ofIso_compat_iff {A B : RigData c ε t} {LA LB : (Limits.pullback c t).Modules} (eA : LA ≅ A.L) (eB : LB ≅ B.L)
    (hA : Scheme.Modules.IsInvertible LA) (hB : Scheme.Modules.IsInvertible LB) (φ : LA ⟶ LB) :
    Compat (A.ofIso LA eA hA) (B.ofIso LB eB hB) φ ↔ Compat A B (eA.inv ≫ φ ≫ eB.hom) := by
  simp only [Compat, ofIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  constructor
  · intro h
    rw [h, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  · intro h
    rw [← cancel_epi ((Scheme.Modules.pullback (rigSection c t ε)).map eA.inv), ← Category.assoc,
      ← Functor.map_comp] at *
    simpa using h

def rigNatIso {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    Scheme.Modules.pullback (baseChangeSnd c ψ) ⋙ Scheme.Modules.pullback (rigSection c t' ε) ≅
      Scheme.Modules.pullback (rigSection c t ε) ⋙ Scheme.Modules.pullback ψ.1 :=
  Scheme.Modules.pullbackComp (rigSection c t' ε) (baseChangeSnd c ψ) ≪≫
    Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε ψ) ≪≫
    (Scheme.Modules.pullbackComp ψ.1 (rigSection c t ε)).symm

def pb (A : RigData c ε t) {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    RigData c ε t' where
  L := (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A.L
  isInvertible := A.isInvertible.pullback _
  α := (rigNatIso ψ).app A.L ≪≫ (Scheme.Modules.pullback ψ.1).mapIso A.α ≪≫ Scheme.Modules.pullbackUnitIso ψ.1

@[scoped simp] lemma pb_L (A : RigData c ε t) {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) : (A.pb ψ).L = (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj A.L := rfl

lemma Compat.pb {A B : RigData c ε t} {φ : A.L ⟶ B.L} (h : Compat A B φ) {T' : Scheme.{u}}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    Compat (A.pb ψ) (B.pb ψ) ((Scheme.Modules.pullback (baseChangeSnd c ψ)).map φ) := by
  simp only [Compat, RigData.pb, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h ⊢
  have hn := (rigNatIso (c := c) (ε := ε) ψ).hom.naturality φ
  simp only [Functor.comp_map] at hn
  have hn' := hn =≫ ((Scheme.Modules.pullback ψ.1).map B.α.hom ≫ (Scheme.Modules.pullbackUnitIso ψ.1).hom)
  simp only [Category.assoc] at hn'
  refine hn'.trans ?_
  have h2 := congrArg (fun k => (rigNatIso (c := c) (ε := ε) ψ).hom.app A.L ≫
    (Scheme.Modules.pullback ψ.1).map k ≫ (Scheme.Modules.pullbackUnitIso ψ.1).hom) h
  simp only [Functor.map_comp, Category.assoc] at h2
  exact h2

end RigData
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

end AlgebraicGeometry.RelPicard.DescentAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

noncomputable section
namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pseudofunctor Surjective Scheme.Modules.pullback Scheme.Pullback.range_fst Spec Scheme Flat Scheme.Modules.pullbackCongr flat_and_surjective_SpecMap_iff Scheme.Modules IsAffineHom Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RigidifiedLineBundle Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp baseChangeSnd_comp rigSection_baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq"
namespace DescentAux
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

open NeronModelInfra CategoryTheory.Pseudofunctor

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

namespace RigData
variable {c ε} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

def ofRLB (M : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ SheafOfModules.unit T.ringCatSheaf) :
    RigData c ε t := ⟨M.L, M.isInvertible, α⟩

def toRLB (A : RigData c ε t) : RigidifiedLineBundle c ε t := ⟨A.L, A.isInvertible, ⟨A.α⟩⟩

lemma exists_compat_iso (A B : RigData c ε t) (h : Nonempty (A.L ≅ B.L)) :
    ∃ φ : A.L ≅ B.L, Compat A B φ.hom := by
  obtain ⟨φ, hφ⟩ := AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
    R c ε t A.toRLB B.toRLB A.α B.α h.some
  exact ⟨φ, (compat_iff_mapIso A B φ).mpr hφ⟩

lemma compat_iso_unique
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A B : RigData c ε t) (φ ψ : A.L ≅ B.L) (hφ : Compat A B φ.hom) (hψ : Compat A B ψ.hom) : φ = ψ :=
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq R c ε hH0 t
    A.toRLB B.toRLB A.α B.α φ ψ ((compat_iff_mapIso A B φ).mp hφ) ((compat_iff_mapIso A B ψ).mp hψ)

lemma compat_hom_unique
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A B : RigData c ε t) (φ ψ : A.L ⟶ B.L) [IsIso φ] [IsIso ψ] (hφ : Compat A B φ) (hψ : Compat A B ψ) :
    φ = ψ :=
  congrArg Iso.hom (compat_iso_unique hH0 A B (asIso φ) (asIso ψ) hφ hψ)

end RigData
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

@[scoped simp] lemma chosenPullback_p {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (chosenPullback c ψ₁ ψ₂).p = baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)) := rfl

def chosenPullback₃' {T T₁ T₂ T₃ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} {t₃ : T₃ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) (ψ₃ : SchemeHomOver t₃ t) :
    ChosenPullback₃ (chosenPullback c ψ₁ ψ₂) (chosenPullback c ψ₂ ψ₃) (chosenPullback c ψ₁ ψ₃) where
  chosenPullback := chosenPullback c (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)
  p := baseChangeSnd c (postComp (postComp ψ₁ (pr₁ ψ₁ ψ₂)) (pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)))
  p₁ := baseChangeSnd c (postComp (pr₁ ψ₁ ψ₂) (pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)))
  p₃ := baseChangeSnd c (postComp (pr₂ ψ₂ ψ₃) (pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)))
  l :=
    { f := baseChangeSnd c
        ⟨pullback.lift ((pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)).1 ≫ (pr₁ ψ₁ ψ₂).1)
            ((pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)).1 ≫ (pr₂ ψ₂ ψ₃).1)
          (by
            have h₁₂ : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 = pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1 := pullback.condition
            have h₂₃ : pullback.fst ψ₂.1 ψ₃.1 ≫ ψ₂.1 = pullback.snd ψ₂.1 ψ₃.1 ≫ ψ₃.1 := pullback.condition
            have h' : pullback.fst (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1) ≫ pullback.snd ψ₁.1 ψ₂.1 =
                pullback.snd (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1) ≫ pullback.fst ψ₂.1 ψ₃.1 :=
              pullback.condition
            simp only [pr₁_val, pr₂_val, Category.assoc]
            rw [h₁₂, ← Category.assoc, h', Category.assoc, h₂₃]),
         by
          simp only [pr₁_val, pr₂_val]
          rw [← Category.assoc, pullback.lift_fst, Category.assoc]
          rfl⟩
      f_p₁ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₁ ψ₁ ψ₃) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_fst _ _ _)
      f_p₂ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₂ ψ₁ ψ₃) = _
        erw [baseChangeSnd_comp]; congr 1; exact Subtype.ext (pullback.lift_snd _ _ _)
      f_p := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₃)) = _
        erw [baseChangeSnd_comp]; congr 1
        exact Subtype.ext (by
          change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ ψ₁.1 = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ ψ₁.1
          rw [pullback.lift_fst_assoc, Category.assoc]
          rfl) }
  hp₁ := by
    change baseChangeSnd c (pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) ≫ baseChangeSnd c (pr₁ ψ₁ ψ₂) = _
    erw [baseChangeSnd_comp]
  hp₃ := by
    change baseChangeSnd c (pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) ≫ baseChangeSnd c (pr₂ ψ₂ ψ₃) = _
    erw [baseChangeSnd_comp]

lemma exists_mem_range_baseChangeSnd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {ι : Type u} {U : ι → Scheme.{u}} {uS : ∀ i, U i ⟶ Spec (CommRingCat.of R)} (f : ∀ i, SchemeHomOver (uS i) t)
    (hf : ∀ x : T, ∃ i, x ∈ Set.range (f i).1.base) (y : ↥(Limits.pullback c t)) :
    ∃ i, y ∈ Set.range (baseChangeSnd c (f i)).base := by
  obtain ⟨i, z, hz⟩ := hf ((pullback.snd c t).base y)
  refine ⟨i, ?_⟩
  have H := isPullback_baseChangeSnd_snd c (f i)
  have hy : y ∈ Set.range (pullback.fst (pullback.snd c t) (f i).1).base := by
    have h := Scheme.Pullback.range_fst (pullback.snd c t) (f i).1
    have hy' : y ∈ (pullback.snd c t).base ⁻¹' Set.range (f i).1.base := ⟨z, hz⟩
    rw [← h] at hy'
    exact hy'
  obtain ⟨w, hw⟩ := hy
  refine ⟨H.isoPullback.inv.base w, ?_⟩
  rw [← hw, ← H.isoPullback_inv_fst]
  rfl

section MODsec

abbrev MOD : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

theorem modMap_toFunctor {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ((MOD).map g.op.toLoc).toFunctor = Scheme.Modules.pullback g := rfl

theorem modMapComp'_eq_mapComp_app {a b d : LocallyDiscrete Scheme.{u}ᵒᵖ} (u : a ⟶ b) (v : b ⟶ d) (M : (MOD).obj a) :
    ((MOD).mapComp' u v (u ≫ v) rfl).hom.toNatTrans.app M = ((MOD).mapComp u v).hom.toNatTrans.app M := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]

theorem modMapComp'_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    ((MOD).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app L =
      (Scheme.Modules.pullbackCongr h.symm).hom.app L ≫ (Scheme.Modules.pullbackComp f g).inv.app L := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact modMapComp'_eq_mapComp_app g.op.toLoc f.op.toLoc L

theorem modMapComp'_inv_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    ((MOD).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app L =
      (Scheme.Modules.pullbackComp f g).hom.app L ≫ (Scheme.Modules.pullbackCongr h).hom.app L := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  have h2 : ((MOD).mapComp' g.op.toLoc f.op.toLoc (g.op.toLoc ≫ f.op.toLoc) rfl).inv.toNatTrans.app L =
      ((MOD).mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app L := by
    rw [Pseudofunctor.mapComp'_eq_mapComp]
  exact h2

def transHom₂ {X₁ X₂ S : Scheme.{u}} (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S) (cp : ChosenPullback q₁ q₂) (L : S.Modules) :
    (Scheme.Modules.pullback cp.p₁).obj ((Scheme.Modules.pullback q₁).obj L) ⟶
      (Scheme.Modules.pullback cp.p₂).obj ((Scheme.Modules.pullback q₂).obj L) :=
  (Scheme.Modules.pullbackComp cp.p₁ q₁).hom.app L ≫ (Scheme.Modules.pullbackCongr cp.hp₁).hom.app L ≫
    (Scheme.Modules.pullbackCongr cp.hp₂.symm).hom.app L ≫ (Scheme.Modules.pullbackComp cp.p₂ q₂).inv.app L

scoped instance isIso_transHom₂ {X₁ X₂ S : Scheme.{u}} (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S) (cp : ChosenPullback q₁ q₂)
    (L : S.Modules) : IsIso (transHom₂ q₁ q₂ cp L) := by
  dsimp only [transHom₂, modMap_toFunctor]
  exact IsIso.comp_isIso' (NatIso.hom_app_isIso _ _) (IsIso.comp_isIso' (NatIso.hom_app_isIso _ _)
    (IsIso.comp_isIso' (NatIso.hom_app_isIso _ _) (NatIso.inv_app_isIso _ _)))

theorem fromDescentData_toDescentData_obj {S : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}} (g : ∀ i, X i ⟶ S)
    (sq : ∀ i j, ChosenPullback (g i) (g j)) (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L : S.Modules) (i : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD) sq sq₃).obj (((MOD).toDescentData g).obj L)).obj i =
      ((MOD).map (g i).op.toLoc).toFunctor.obj L := rfl

set_option backward.defeqAttrib.useBackward true in
theorem fromDescentData_toDescentData_hom {S : Scheme.{u}} {ι : Type v} {X : ι → Scheme.{u}} (g : ∀ i, X i ⟶ S)
    (sq : ∀ i j, ChosenPullback (g i) (g j)) (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L : S.Modules) (i j : ι) :
    ((DescentData'.fromDescentDataFunctor (MOD) sq sq₃).obj (((MOD).toDescentData g).obj L)).hom i j =
      transHom₂ (g i) (g j) (sq i j) L := by
  rw [FourCorner.DescentDataPrimeComputation.from_to_hom]
  change _ = transHom₂ (g i) (g j) (sq i j) L
  unfold transHom₂
  rw [modMapComp'_inv_app (sq i j).p₁ (g i) L (sq i j).p (sq i j).hp₁,
    modMapComp'_hom_app (sq i j).p₂ (g j) L (sq i j).p (sq i j).hp₂]
  exact Category.assoc _ _ _

end MODsec
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

section bridge

variable {c ε}
variable {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
  {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t)

lemma bc_pr₁_comp : baseChangeSnd c (pr₁ ψ₁ ψ₂) ≫ baseChangeSnd c ψ₁ = baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)) :=
  baseChangeSnd_comp c _ _

lemma bc_pr₂_comp : baseChangeSnd c (pr₂ ψ₁ ψ₂) ≫ baseChangeSnd c ψ₂ = baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)) := by
  rw [baseChangeSnd_comp, ← postComp_pr₁_eq_postComp_pr₂]

lemma pr₁_comp_val : (pr₁ ψ₁ ψ₂).1 ≫ ψ₁.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 := rfl

lemma pr₂_comp_val : (pr₂ ψ₁ ψ₂).1 ≫ ψ₂.1 = (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1 := pullback.condition.symm

variable (c) in

abbrev rawHom (L : (Limits.pullback c t).Modules) :
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj L) ⟶
      (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj L) :=
  transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) (chosenPullback c ψ₁ ψ₂) L

theorem transHom₂_eq_rawHom (L : (Limits.pullback c t).Modules) :
    transHom₂ (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) (chosenPullback c ψ₁ ψ₂) L = rawHom c ψ₁ ψ₂ L := rfl

