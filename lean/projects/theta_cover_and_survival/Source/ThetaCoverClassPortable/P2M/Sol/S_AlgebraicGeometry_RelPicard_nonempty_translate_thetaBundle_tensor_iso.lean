import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import ThetaCoverClassPortable.Definitions.Def_JacJ1Iface
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_thetaBundle_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import ThetaCoverClassPortable.ActualRigidifiedFibreTwistQQ
import ThetaCoverClassPortable.ActualAllModelGenusBaseChange
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_translate_thetaBundle_tensor_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_translate_thetaBundle_tensor_iso.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_nonempty_translate_thetaBundle_tensor_iso.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian AlgebraicCurve~genus"

open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral LocallyOfFiniteType Spec Scheme Smooth Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules GeometricallyConnected Scheme.Modules.pullbackComp RelPicard.RigidifiedLineBundle Scheme.Modules.pullbackTensorObjIso SmoothProperCurve.FiniteMapData RelPicard.nonempty_pullback_thetaBundle_iso   RelPicard.nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd postComp baseChangeSnd_id baseChangeSnd_comp RigidifiedLineBundle RepresentsRelSubPic fibreAt FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut sectionTwist thetaBundle fibreModule nonempty_pullback_thetaBundle_iso RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso  nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero"
namespace RigidifiedLineBundle
p2m_export "AlgebraicGeometry.RelPicard.RigidifiedLineBundle" "pullbackAlong L mk tensor"
p2m_open "AlgebraicGeometry.RelPicard.RigidifiedLineBundle AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

private noncomputable def _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle.sqCongrL {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (ψ ψ' : SchemeHomOver t' t) (h : ψ.1 = ψ'.1) :
    (M.pullbackAlong ψ).L ≅ (M.pullbackAlong ψ').L :=
  (Scheme.Modules.pullbackCongr (show baseChangeSnd c ψ = baseChangeSnd c ψ' by rw [Subtype.ext h])).app M.L

p2m_export "AlgebraicGeometry.RelPicard.RigidifiedLineBundle" "sqCongrL"

private noncomputable def _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle.sqCompL {X X' T' : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of R)} {x' : X' ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε x') (φ : SchemeHomOver x x')
    (ψ : SchemeHomOver t' x) :
    ((M.pullbackAlong φ).pullbackAlong ψ).L ≅ (M.pullbackAlong (postComp φ ψ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) (baseChangeSnd c φ)).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c φ ψ)).app M.L

p2m_export "AlgebraicGeometry.RelPicard.RigidifiedLineBundle" "sqCompL"

private noncomputable def _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle.sqIdL {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t)
    (ψ : SchemeHomOver t t) (h : ψ.1 = 𝟙 T) : (M.pullbackAlong ψ).L ≅ M.L :=
  M.sqCongrL ψ ⟨𝟙 T, Category.id_comp t⟩ h ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_id c t)).app M.L ≪≫ (Scheme.Modules.pullbackId _).app M.L

p2m_export "AlgebraicGeometry.RelPicard.RigidifiedLineBundle" "sqIdL"

noncomputable def sqTensorL {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (L M : RigidifiedLineBundle c ε t) :
    ((L.tensor M).pullbackAlong ψ).L ≅ ((L.pullbackAlong ψ).tensor (M.pullbackAlong ψ)).L :=
  Scheme.Modules.pullbackTensorObjIso _ _ _

end AlgebraicGeometry.RelPicard.RigidifiedLineBundle

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra ℚ k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (J : RelativePic0Designation k c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    (hsm : Smooth J.toBase) (hpr : IsProper J.toBase) (hgc : GeometricallyConnected J.toBase)
    (g : ℕ)
    (hg : FourCorner.ActualPicardProperties.AllModelRRGenus c g)
    (r : ℕ) (hr : 2 * g ≤ r)
    (x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) :
    letI := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).grpObj
    Nonempty (
      (Scheme.Modules.pullback
          (𝟙 (Over.mk J.toBase) * (CartesianMonoidalCategory.toUnit (Over.mk J.toBase) ≫ x)).left).obj
        (thetaBundle c ε J.toBase h.poincare r (r + 1 - g)) ⊗
      (Scheme.Modules.pullback
          (𝟙 (Over.mk J.toBase) * (CartesianMonoidalCategory.toUnit (Over.mk J.toBase) ≫ y)).left).obj
        (thetaBundle c ε J.toBase h.poincare r (r + 1 - g)) ≅
      (Scheme.Modules.pullback
          (𝟙 (Over.mk J.toBase) * (CartesianMonoidalCategory.toUnit (Over.mk J.toBase) ≫ (x * y))).left).obj
        (thetaBundle c ε J.toBase h.poincare r (r + 1 - g)) ⊗
      thetaBundle c ε J.toBase h.poincare r (r + 1 - g)) := by

  let h' : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J := h
  letI := h'.grpObj
  haveI : IsProper J.toBase := hpr
  haveI : LocallyOfFiniteType J.toBase := inferInstance

  let S := Spec (CommRingCat.of k)
  let JB : Over S := Over.mk J.toBase
  let P : RigidifiedLineBundle c ε J.toBase := h.poincare
  let tJ : SchemeHomOver J.toBase (𝟙 S) := ⟨J.toBase, Category.comp_id _⟩

  let T : (Over.mk (𝟙 S) ⟶ JB) → (JB ⟶ JB) := fun a => 𝟙 JB * (CartesianMonoidalCategory.toUnit JB ≫ a)
  let ov : (JB ⟶ JB) → SchemeHomOver J.toBase J.toBase := fun f => ⟨f.left, Over.w f⟩
  let N : (Over.mk (𝟙 S) ⟶ JB) → RigidifiedLineBundle c ε (𝟙 S) := fun a => P.pullbackAlong ⟨a.left, Over.w a⟩
  have htu : (CartesianMonoidalCategory.toUnit JB).left = J.toBase := by
    first
      | simp [JB]
      | simpa [JB] using Over.w (CartesianMonoidalCategory.toUnit JB)
      | (have w := Over.w (CartesianMonoidalCategory.toUnit JB)
         simp only [JB, Over.mk_left, Over.mk_hom] at w ⊢
         simpa using w)

  obtain ⟨𝔉, -⟩ := h𝔉 0
  have hgeo := hg
  have hfib : ∀ (M : RigidifiedLineBundle c ε J.toBase), FibrewiseAlgEquivZero M →
      ∀ (k' : Type u) [Field k'] (s : Spec (CommRingCat.of k') ⟶ J.P)
        (𝒲 : (pullback (pullback.snd c J.toBase) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c J.toBase s) (fibreModule c J.toBase s (M.L ⊗ sectionTwist c ε J.toBase r))).H1 ∧
          Module.finrank k' (𝒲.sectionsOf (fibreAt c J.toBase s)
            (fibreModule c J.toBase s (M.L ⊗ sectionTwist c ε J.toBase r))).H0 = r + 1 - g :=
    fun M hM => P2MW.ActualRigidifiedFibreTwistQQ.solution
      k c ε (algebraMap ℚ k) 𝔉 g hgeo M hM r (by omega)
  have hP : FibrewiseAlgEquivZero P := h.poincare_mem

  have jj : ∀ a : Over.mk (𝟙 S) ⟶ JB, ((N a).pullbackAlong tJ).L ≅
      (h'.poincare.pullbackAlong (ov (CartesianMonoidalCategory.toUnit JB ≫ a))).L := fun a =>
    P.sqCompL ⟨a.left, Over.w a⟩ tJ ≪≫ P.sqCongrL _ _
      (show J.toBase ≫ a.left = (CartesianMonoidalCategory.toUnit JB ≫ a).left from (congrArg (· ≫ a.left) htu).symm)

  have e : ∀ a : Over.mk (𝟙 S) ⟶ JB, (P.tensor ((N a).pullbackAlong tJ)).L ≅ (P.pullbackAlong (ov (T a))).L :=
    fun a => ((P.sqIdL (ov (𝟙 JB)) rfl).symm ⊗ᵢ jj a) ≪≫
      (RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso h' (𝟙 JB)
        (CartesianMonoidalCategory.toUnit JB ≫ a)).some.symm

  have Φ : ∀ a : Over.mk (𝟙 S) ⟶ JB,
      (Scheme.Modules.pullback (T a).left).obj (thetaBundle c ε J.toBase P r (r + 1 - g)) ≅
        thetaBundle c ε J.toBase (P.tensor ((N a).pullbackAlong tJ)) r (r + 1 - g) := fun a =>
    (RelPicard.nonempty_pullback_thetaBundle_iso k c ε h𝔉 P r (r + 1 - g) (hfib P hP) (ov (T a))
      (P.tensor ((N a).pullbackAlong tJ)) (e a)).some

  have hmul : CartesianMonoidalCategory.toUnit JB ≫ (x * y) =
      (CartesianMonoidalCategory.toUnit JB ≫ x) * (CartesianMonoidalCategory.toUnit JB ≫ y) :=
    MonObj.comp_mul _ _ _
  have exy : (P.tensor (((N x).tensor (N y)).pullbackAlong tJ)).L ≅ (P.pullbackAlong (ov (T (x * y)))).L :=
    ((P.sqIdL (ov (𝟙 JB)) rfl).symm ⊗ᵢ
      (RigidifiedLineBundle.sqTensorL tJ (N x) (N y) ≪≫ (jj x ⊗ᵢ jj y) ≪≫
        (RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso h'
          (CartesianMonoidalCategory.toUnit JB ≫ x) (CartesianMonoidalCategory.toUnit JB ≫ y)).some.symm ≪≫
        h'.poincare.sqCongrL _ _ (congrArg (fun f : JB ⟶ JB => f.left) hmul).symm)) ≪≫
      (RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso h' (𝟙 JB)
        (CartesianMonoidalCategory.toUnit JB ≫ (x * y))).some.symm
  have Φxy : (Scheme.Modules.pullback (T (x * y)).left).obj (thetaBundle c ε J.toBase P r (r + 1 - g)) ≅
      thetaBundle c ε J.toBase (P.tensor (((N x).tensor (N y)).pullbackAlong tJ)) r (r + 1 - g) :=
    (RelPicard.nonempty_pullback_thetaBundle_iso k c ε h𝔉 P r (r + 1 - g) (hfib P hP) (ov (T (x * y)))
      (P.tensor (((N x).tensor (N y)).pullbackAlong tJ)) exy).some

  obtain ⟨lin⟩ := RelPicard.nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero k c ε h𝔉 g
    hgeo P hP (N x) (N y) (hP.pullback _) (hP.pullback _) r (by omega)
  exact ⟨(Φ x ⊗ᵢ Φ y) ≪≫ lin ≪≫ (Φxy.symm ⊗ᵢ Iso.refl _)⟩
