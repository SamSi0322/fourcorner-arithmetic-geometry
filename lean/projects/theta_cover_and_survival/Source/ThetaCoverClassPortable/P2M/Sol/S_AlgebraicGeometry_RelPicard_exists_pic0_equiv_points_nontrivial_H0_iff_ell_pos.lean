import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Topology.Sheaves.LocallySurjective
import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import ThetaCoverClassPortable.Definitions.Def_JacJ1Iface
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_IsCurveOver
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_sup_eq_top
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_iff_ell_pos

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_iff_ell_pos.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_iff_ell_pos.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian AlgebraicCurve"

open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral Spec Scheme Scheme.Modules toSpecΓ geometrically Scheme.TwoAffineOpenCover RelPicard.exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos RelPicard.exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RepresentsRelSubPic fibreAt algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.grpObj sectionTwist fibreModule exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso"
namespace ThetaDictGlue
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_twoAffineOpenCover_of_iso {X X' : Scheme.{u}} (φ : X ≅ X') (𝒱' : X'.TwoAffineOpenCover) :
    Nonempty X.TwoAffineOpenCover := by

  obtain ⟨𝒱, -, -, -, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (R := Γ(X', ⊤)) (φ.hom ≫ X'.toSpecΓ) X'.toSpecΓ φ rfl 𝒱' (𝟙_ X'.Modules)
    ((Scheme.Modules.pullback φ.hom).obj (𝟙_ X'.Modules)) (Iso.refl _)
  exact ⟨𝒱⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_twoAffineOpenCover_curveModel {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    (M : CurveModel k F) : Nonempty M.C.TwoAffineOpenCover := by
  obtain ⟨U, V, hU, hV, hUV, hsup⟩ := AlgebraicCurve.exists_isAffineOpen_sup_eq_top M.toBase M.finset_subset_affineOpen
  exact ⟨{ U0 := U, U1 := V, isAffineOpen_U0 := hU, isAffineOpen_U1 := hV, sup_eq_top := hsup, isAffineOpen_inf := hUV }⟩

end AlgebraicGeometry.RelPicard.ThetaDictGlue

open AlgebraicGeometry.RelPicard.ThetaDictGlue in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (J : RelativePic0Designation k c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    {F : Type u} [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (M : CurveModel k F) (e : M.C ≅ C) (he : e.hom ≫ c = M.toBase)
    (ε' : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (hε' : ε'.1 ≫ e.hom = ε.1) :
    letI := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).grpObj
    ∃ pts : Pic0 k F ≃ (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase),
      (∀ a b : Pic0 k F, pts (a + b) = pts a * pts b) ∧
      ∀ (Dv : Divisor.degZero (K := k) (F := F)) (d : ℕ),
        (∀ 𝒲 : (pullback (pullback.snd c J.toBase) (pts (Pic0.mk Dv)).left).TwoAffineOpenCover,
            Nontrivial (𝒲.sectionsOf (fibreAt c J.toBase (pts (Pic0.mk Dv)).left)
              (fibreModule c J.toBase (pts (Pic0.mk Dv)).left
                (h.poincare.L ⊗ sectionTwist c ε J.toBase d))).H0) ↔
          0 < ell ((Dv : Divisor k F) + Finsupp.single (M.pointEquivPlace ε') (d : ℤ)) := by
  obtain ⟨pts, hhom, hcore⟩ :=
    AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos k c ε 𝔉 J h M e he ε' hε'
  refine ⟨pts, hhom, fun Dv d => ?_⟩

  have hx : (pts (Pic0.mk Dv)).left ≫ J.toBase = 𝟙 (Spec (CommRingCat.of k)) := by
    have w := Over.w (pts (Pic0.mk Dv)); simp only [Over.mk_left, Over.mk_hom] at w; exact w
  obtain ⟨φ, hφ₁, -, hφ₃⟩ :=
    AlgebraicGeometry.RelPicard.exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso c ε J.toBase
      (pts (Pic0.mk Dv)).left hx
  obtain ⟨eF⟩ := hφ₃ h.poincare.L d

  obtain ⟨𝒱M⟩ := nonempty_twoAffineOpenCover_curveModel M
  obtain ⟨𝒱C⟩ := nonempty_twoAffineOpenCover_of_iso e.symm 𝒱M
  obtain ⟨𝒲₀⟩ := nonempty_twoAffineOpenCover_of_iso φ.symm 𝒱C
  constructor
  · intro hfib
    obtain ⟨a, b, hab⟩ := hfib 𝒲₀
    obtain ⟨𝒱, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      c (fibreAt c J.toBase (pts (Pic0.mk Dv)).left) φ hφ₁ 𝒲₀ _ _ eF.symm
    exact (hcore Dv d 𝒱).mp ⟨e0.symm a, e0.symm b, fun hh => hab (e0.symm.injective hh)⟩
  · intro hell 𝒲
    obtain ⟨𝒱, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      c (fibreAt c J.toBase (pts (Pic0.mk Dv)).left) φ hφ₁ 𝒲 _ _ eF.symm
    obtain ⟨a, b, hab⟩ := (hcore Dv d 𝒱).mpr hell
    exact ⟨e0 a, e0 b, fun hh => hab (e0.injective hh)⟩
