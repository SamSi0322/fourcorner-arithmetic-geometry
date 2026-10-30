import ThetaCoverClassPortable.RigidifiedFFIsoLegs
import ThetaCoverClassPortable.RigidifiedFFIsoHeadFormal
import ThetaCoverClassPortable.RigidifiedFFIsoNativeLift
import ThetaCoverClassPortable.DescentDataPrimeIsoLifting
import ThetaCoverClassPortable.DescentFunctorCoherence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open CategoryTheory.Pseudofunctor
universe u v
namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry"
noncomputable section
namespace AlgebraicGeometry.RelPicard.DescentAux
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"
open NeronModelInfra
variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
section bridge
variable {c ε}
variable {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
  {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
  (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t)
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
lemma map_rawHom_comp_legIso (L : (Limits.pullback c t).Modules) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map (rawHom c ψ₁ ψ₂ L) ≫
        (legIso ψ₁ ψ₂ ψ₂ (pr₂ ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂) L).hom =
      (legIso ψ₁ ψ₂ ψ₁ (pr₁ ψ₁ ψ₂) (pr₁_comp_val ψ₁ ψ₂) L).hom := by
  exact FourCorner.RigidifiedFFIsoHeadFormal.solution
    (baseChangeSnd c (pr₁ ψ₁ ψ₂)) (baseChangeSnd c ψ₁)
    (baseChangeSnd c (pr₂ ψ₁ ψ₂)) (baseChangeSnd c ψ₂)
    (baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂)))
    (bc_pr₁_comp (c := c) ψ₁ ψ₂) (bc_pr₂_comp (c := c) ψ₁ ψ₂)
    (rigSection c (strMap₁₂ ψ₁ ψ₂) ε) (rigSection c t₁ ε) (rigSection c t₂ ε) (rigSection c t ε)
    (pr₁ ψ₁ ψ₂).1 ψ₁.1 (pr₂ ψ₁ ψ₂).1 ψ₂.1 (postComp ψ₁ (pr₁ ψ₁ ψ₂)).1
    (pr₁_comp_val ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂)
    (rigSection_baseChangeSnd c ε (pr₁ ψ₁ ψ₂)) (rigSection_baseChangeSnd c ε ψ₁)
    (rigSection_baseChangeSnd c ε (pr₂ ψ₁ ψ₂)) (rigSection_baseChangeSnd c ε ψ₂) L
    (rawHom c ψ₁ ψ₂ L)
    (legIso ψ₁ ψ₂ ψ₁ (pr₁ ψ₁ ψ₂) (pr₁_comp_val ψ₁ ψ₂) L)
    (legIso ψ₁ ψ₂ ψ₂ (pr₂ ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂) L)
    rfl (legIso_eq_sqIso ψ₁ ψ₂ ψ₁ (pr₁ ψ₁ ψ₂) (pr₁_comp_val ψ₁ ψ₂) L)
    (legIso_eq_sqIso ψ₁ ψ₂ ψ₂ (pr₂ ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂) L)

theorem map_comp_rawHom_eq
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (A₁ A₂ : RigData c ε t)
    (φ₁ : (Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₁.L ⟶ (Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₂.L)
    (φ₂ : (Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₁.L ⟶ (Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₂.L)
    [IsIso φ₁] [IsIso φ₂]
    (h₁ : RigData.Compat (A₁.pb ψ₁) (A₂.pb ψ₁) φ₁) (h₂ : RigData.Compat (A₁.pb ψ₂) (A₂.pb ψ₂) φ₂) :
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).map φ₁ ≫ rawHom c ψ₁ ψ₂ A₂.L =
      rawHom c ψ₁ ψ₂ A₁.L ≫ (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).map φ₂ := by
  have key : (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map
      ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).map φ₁ ≫ rawHom c ψ₁ ψ₂ A₂.L) =
      (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map
      (rawHom c ψ₁ ψ₂ A₁.L ≫ (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).map φ₂) := by
    have H1 := map_rawHom_comp_legIso (c := c) (ε := ε) ψ₁ ψ₂ A₁.L
    have H2 := map_rawHom_comp_legIso (c := c) (ε := ε) ψ₁ ψ₂ A₂.L
    have H2' : (legIso ψ₁ ψ₂ ψ₁ (pr₁ ψ₁ ψ₂) (pr₁_comp_val ψ₁ ψ₂) A₂.L).inv ≫
        (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).map (rawHom c ψ₁ ψ₂ A₂.L) =
        (legIso ψ₁ ψ₂ ψ₂ (pr₂ ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂) A₂.L).inv :=
      (Iso.inv_comp_eq _).mpr ((Iso.eq_comp_inv _).mpr H2)
    rw [Functor.map_comp, Functor.map_comp,
      map_map_eq_legIso_conj ψ₁ ψ₂ ψ₁ (pr₁ ψ₁ ψ₂) (pr₁_comp_val ψ₁ ψ₂) A₁ A₂ φ₁ h₁,
      map_map_eq_legIso_conj ψ₁ ψ₂ ψ₂ (pr₂ ψ₁ ψ₂) (pr₂_comp_val ψ₁ ψ₂) A₁ A₂ φ₂ h₂]
    simp only [Category.assoc]
    rw [H2', ← H1, Category.assoc]

  let Φ : ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₁.L) ≅
          (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₂.L)) :=
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).mapIso (asIso φ₁) ≪≫ asIso (rawHom c ψ₁ ψ₂ A₂.L)
  let Ψ : ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₁)).obj A₁.L) ≅
          (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ₂)).obj A₂.L)) :=
    asIso (rawHom c ψ₁ ψ₂ A₁.L) ≪≫ (Scheme.Modules.pullback (baseChangeSnd c (pr₂ ψ₁ ψ₂))).mapIso (asIso φ₂)
  have hΨ : (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Ψ ≪≫ ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α =
      (Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Φ ≪≫ ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α :=
    Iso.ext (by
      first
        | simpa only [Φ, Ψ, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Functor.map_comp, Category.assoc] using
            congrArg (· ≫ ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α.hom) key.symm
        | (change (Scheme.Modules.pullback _).map
              (rawHom c ψ₁ ψ₂ A₁.L ≫ (Scheme.Modules.pullback _).map φ₂) ≫ _ =
              (Scheme.Modules.pullback _).map
                ((Scheme.Modules.pullback _).map φ₁ ≫ rawHom c ψ₁ ψ₂ A₂.L) ≫ _
           rw [key]))
  have hΦΨ : Φ = Ψ :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.iso_eq_of_map_pullback_rigSection_comp_eq R c ε hH0
      (strMap₁₂ ψ₁ ψ₂) ((A₁.pb ψ₁).pb (pr₁ ψ₁ ψ₂)).toRLB ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).toRLB
      ((Scheme.Modules.pullback (rigSection c (strMap₁₂ ψ₁ ψ₂) ε)).mapIso Φ ≪≫ ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α)
      ((A₂.pb ψ₂).pb (pr₂ ψ₁ ψ₂)).α Φ Ψ rfl hΨ
  exact congrArg Iso.hom hΦΨ

end bridge
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

section asm_b

open AlgebraicGeometry.SmoothProperCurve

variable (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

abbrev πS : SchemeHomOver (pullback.snd t (specMap R R') ≫ specMap R R') t :=
  ⟨pullback.fst t (specMap R R'), pullback.condition⟩

scoped instance flat_specMap : Flat (specMap R R') :=
  ((flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).1
scoped instance surjective_specMap : Surjective (specMap R R') :=
  ((flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2

scoped instance isAffineHom_πS : IsAffineHom (πS (R := R) R' t).1 :=
  MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance

scoped instance isAffineHom_q : IsAffineHom (baseChangeSnd c (πS R' t)) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeSnd_snd c (πS R' t)).flip inferInstance
scoped instance flat_q : Flat (baseChangeSnd c (πS R' t)) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeSnd_snd c (πS R' t)).flip inferInstance
scoped instance surjective_q : Surjective (baseChangeSnd c (πS R' t)) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeSnd_snd c (πS R' t)).flip inferInstance

abbrev sq : ∀ (_ _ : Unit), ChosenPullback (baseChangeSnd c (πS R' t)) (baseChangeSnd c (πS R' t)) :=
  fun _ _ => chosenPullback c (πS R' t) (πS R' t)
abbrev sq₃ : ∀ (i₁ i₂ i₃ : Unit), ChosenPullback₃ (sq c R' t i₁ i₂) (sq c R' t i₂ i₃) (sq c R' t i₁ i₃) :=
  fun _ _ _ => chosenPullback₃ c (πS R' t)

set_option maxHeartbeats 16000000 in
set_option backward.isDefEq.respectTransparency.types true in
theorem asm_b
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (M₁ M₂ : RigidifiedLineBundle c ε t)
    (h : Nonempty ((M₁.pullbackAlong (πS R' t)).L ≅ (M₂.pullbackAlong (πS R' t)).L)) :
    Nonempty (M₁.L ≅ M₂.L) := by

  let A₁ : RigData c ε t := RigData.ofRLB M₁ M₁.rigidified.some
  let A₂ : RigData c ε t := RigData.ofRLB M₂ M₂.rigidified.some

  obtain ⟨ι', hι'⟩ := RigData.exists_compat_iso (A₁.pb (πS R' t)) (A₂.pb (πS R' t)) h

  have comm := map_comp_rawHom_eq (πS R' t) (πS R' t) hH0 A₁ A₂
    ι'.hom ι'.hom hι' hι'
  apply FourCorner.RigidifiedFFIsoNativeLift.affine
    (baseChangeSnd c (πS R' t)) (sq c R' t) (sq₃ c R' t)
    M₁.L M₂.L M₁.isInvertible M₂.isInvertible (fun _ => ι') ?_
  intro i j
  change (Scheme.Modules.pullback (baseChangeSnd c (pr₁ (πS R' t) (πS R' t)))).map ι'.hom ≫
      rawHom c (πS R' t) (πS R' t) M₂.L =
    rawHom c (πS R' t) (πS R' t) M₁.L ≫
      (Scheme.Modules.pullback (baseChangeSnd c (pr₂ (πS R' t) (πS R' t)))).map ι'.hom
  exact comm

end asm_b
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

end AlgebraicGeometry.RelPicard.DescentAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"
end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard.DescentAux.RigData"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra"

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M₁ M₂ : RigidifiedLineBundle c ε t)
    (h : Nonempty ((M₁.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩).L ≅
      (M₂.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩).L)) :
    Nonempty (M₁.L ≅ M₂.L) :=
  AlgebraicGeometry.RelPicard.DescentAux.asm_b c ε R' t hH0 M₁ M₂ h
