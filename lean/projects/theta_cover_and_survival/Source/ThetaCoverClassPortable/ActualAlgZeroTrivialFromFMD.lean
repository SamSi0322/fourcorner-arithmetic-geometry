import ThetaCoverClassPortable.ActualAlgEquivZeroEulerIff
import ThetaCoverClassPortable.FieldZeroDivisorBase
import ThetaCoverClassPortable.FiniteMapDataBaseChange
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RelCartier
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ThetaCoverClassPortable.P2M.Util
namespace FourCorner.ActualAlgZeroTrivialFromFMD

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard"

namespace AlgZeroTrivGlue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

noncomputable def isoUnitOfIdempotentOfInverse {C : Type*} [Category C] [MonoidalCategory C] {N M : C}
    (e : N ≅ N ⊗ N) (p : N ⊗ M ≅ 𝟙_ C) : N ≅ 𝟙_ C :=
  (ρ_ N).symm ≪≫ whiskerLeftIso N p.symm ≪≫ (α_ N N M).symm ≪≫ whiskerRightIso e.symm M ≪≫ p

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_invModule_top_iso (Y : Scheme.{u}) :
    Nonempty ((⊤ : Y.IdealSheafData).invModule ≅ 𝟙_ Y.Modules) := by
  have hT : (⊤ : Y.IdealSheafData).IsInvertible := Scheme.IdealSheafData.isInvertible_top

  obtain ⟨m⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hT hT
  have e : (⊤ : Y.IdealSheafData).invModule ≅ (⊤ : Y.IdealSheafData).invModule ⊗ (⊤ : Y.IdealSheafData).invModule :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule (Scheme.IdealSheafData.mul_top ⊤).symm) ≪≫ m

  have hN : Scheme.Modules.IsInvertible (⊤ : Y.IdealSheafData).invModule :=
    Scheme.IdealSheafData.IsInvertible.isInvertible_invModule hT
  obtain ⟨hdual,⟨pairing⟩⟩ := hN.dual
  exact ⟨isoUnitOfIdempotentOfInverse e pairing⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_lineBundle_iso_of_degree_zero {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f 0 g) : Nonempty (D.lineBundle ≅ 𝟙_ (pullback f g).Modules) := by
  obtain ⟨e⟩ := nonempty_invModule_top_iso (pullback f g)
  exact ⟨eqToIso (congrArg Scheme.IdealSheafData.invModule D.I_eq_top_of_degree_zero) ≪≫ e⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

noncomputable def isoPullbackInvPullbackObj {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] (L : Y.Modules) :
    L ≅ (Scheme.Modules.pullback (inv p)).obj ((Scheme.Modules.pullback p).obj L) :=
  ((Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).app L).symm

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem eq_zero_of_pullback_map_eq_zero {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p]
    {A B : Y.Modules} (φ : A ⟶ B) (h : (Scheme.Modules.pullback p).map φ = 0) : φ = 0 := by

  have hn : (Scheme.Modules.pullback (inv p)).map ((Scheme.Modules.pullback p).map φ) ≫
      (isoPullbackInvPullbackObj p B).inv = (isoPullbackInvPullbackObj p A).inv ≫ φ :=
    (Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).hom.naturality φ
  rw [h, Functor.map_zero, zero_comp] at hn
  exact (cancel_epi (isoPullbackInvPullbackObj p A).inv).mp (hn.symm.trans (comp_zero).symm)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem pullbackSection_ne_zero {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] {M : Y.Modules}
    (s : 𝟙_ Y.Modules ⟶ M) (hs : s ≠ 0) : Scheme.Modules.pullbackSection p s ≠ 0 := by
  intro h
  apply hs
  apply eq_zero_of_pullback_map_eq_zero p

  exact ((Scheme.Modules.pullbackUnitIso p).hom_inv_id_assoc ((Scheme.Modules.pullback p).map s)).symm.trans
    ((congrArg ((Scheme.Modules.pullbackUnitIso p).hom ≫ ·) h).trans comp_zero)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem twoAffineOpenCover_ext {Y : Scheme.{u}} {𝒲 𝒲' : Y.TwoAffineOpenCover}
    (h0 : 𝒲.U0 = 𝒲'.U0) (h1 : 𝒲.U1 = 𝒲'.U1) : 𝒲 = 𝒲' := by
  obtain ⟨U0, U1, _, _, _, _⟩ := 𝒲
  obtain ⟨U0', U1', _, _, _, _⟩ := 𝒲'
  dsimp only at h0 h1
  subst h0
  subst h1
  rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem preimage_id_opens {Y : Scheme.{u}} (U : Y.Opens) : (𝟙 Y) ⁻¹ᵁ U = U := rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem eulerChar_congr {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    (𝒲 : Y.TwoAffineOpenCover) {M M' : Y.Modules} (e : M ≅ M') :
    (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1
      = (Module.finrank k (𝒲.sectionsOf y M').H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M').H1 := by
  obtain ⟨𝒲', h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y y (Iso.refl Y) (Category.id_comp y)
      𝒲 M' M (e ≪≫ ((Scheme.Modules.pullbackId Y).app M').symm)
  have h𝒲 : 𝒲' = 𝒲 :=
    twoAffineOpenCover_ext (h0.trans (preimage_id_opens _)) (h1.trans (preimage_id_opens _))
  subst h𝒲
  exact congrArg₂ (fun m n : ℕ => (m : ℤ) - (n : ℤ)) e0.finrank_eq e1.finrank_eq

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_iso_tensorUnit_fibre
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of R)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε)
    {k : Type u} [Field k] (x : Spec (.of k) ⟶ Spec (.of R))
    {M : (pullback c x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (h0 : IsAlgEquivZero (pullback.snd c x) M)
    (s : 𝟙_ (pullback c x).Modules ⟶ M) (hs : s ≠ 0) (V : (pullback c x).TwoAffineOpenCover) :
    Nonempty (M ≅ 𝟙_ (pullback c x).Modules) := by
  obtain ⟨a,ha⟩ := Spec.map_surjective x
  letI : Algebra R k := a.hom.toAlgebra
  have hx : Scheme.TwoAffineOpenCover.specMap R k = x := ha
  subst x
  let x := Scheme.TwoAffineOpenCover.specMap R k
  haveI : IsProper (pullback.snd c x) := inferInstance
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c x) := MorphismProperty.pullback_snd c x inferInstance
  have hχ := FourCorner.ActualAlgEquivZeroEulerIff.eulerChar_eq_of_isAlgEquivZero k (pullback.snd c x)
    (SmoothProperCurve.sectionBaseChange k ε) (F.baseChange k) M hM V h0
  obtain ⟨D,-,⟨e,-⟩⟩ := FourCorner.FieldZeroDivisor.exists_zero_divisor_over_field_of_finiteMapData F x hM s hs V 0
    (by rw [Nat.cast_zero,add_zero];exact hχ)
  obtain ⟨e0⟩ := nonempty_lineBundle_iso_of_degree_zero D
  exact ⟨e ≪≫ e0⟩

end AlgZeroTrivGlue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIntegral x]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 _) x) (F : SmoothProperCurve.FiniteMapData x ε)
    (𝒱 : X.TwoAffineOpenCover) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (h0 : IsAlgEquivZero x L) (s : 𝟙_ X.Modules ⟶ L) (hs : s ≠ 0) :
    Nonempty (L ≅ 𝟙_ X.Modules) := by

  have hp : pullback.fst x (𝟙 _) ≫ x = pullback.snd x (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.condition.trans (Category.comp_id _)

  obtain ⟨𝒱', -, -, -, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd x (𝟙 (Spec (CommRingCat.of k)))) x (asIso (pullback.fst x (𝟙 _))) hp 𝒱 L
    ((Scheme.Modules.pullback (pullback.fst x (𝟙 _))).obj L) (Iso.refl _)

  obtain ⟨e⟩ := AlgZeroTrivGlue.nonempty_iso_tensorUnit_fibre x ε F (𝟙 _) (hL.pullback _) (h0.pullback _ hp)
    (Scheme.Modules.pullbackSection _ s) (AlgZeroTrivGlue.pullbackSection_ne_zero _ s hs) 𝒱'

  exact ⟨AlgZeroTrivGlue.isoPullbackInvPullbackObj (pullback.fst x (𝟙 _)) L ≪≫ (Scheme.Modules.pullback _).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso _⟩

#print axioms solution
end FourCorner.ActualAlgZeroTrivialFromFMD
