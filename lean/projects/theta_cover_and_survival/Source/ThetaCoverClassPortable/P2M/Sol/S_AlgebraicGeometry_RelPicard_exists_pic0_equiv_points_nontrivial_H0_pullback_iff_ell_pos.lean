import ThetaCoverClassPortable.ActualPic0DictionaryFMD
noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve
open scoped CategoryTheory.MonObj
namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos
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
      ∀ (Dv : Divisor.degZero (K := k) (F := F)) (d : ℕ) (𝒱 : C.TwoAffineOpenCover),
        Nontrivial (𝒱.sectionsOf c
          ((Scheme.Modules.pullback
              (pullback.lift (𝟙 C) (c ≫ (pts (Pic0.mk Dv)).left)
                (((Category.id_comp c).trans (Category.comp_id c).symm).trans
                  ((congrArg (c ≫ ·) (Over.w (pts (Pic0.mk Dv)))).symm.trans
                    (Category.assoc c _ _).symm)))).obj h.poincare.L ⊗
            ((ε.1.ker) ^ d).invModule)).H0 ↔
          0 < ell ((Dv : Divisor k F) + Finsupp.single (M.pointEquivPlace ε') (d : ℤ)) := by
  obtain ⟨pts,hadd,_,hread⟩ := P2MW.ActualPic0DictionaryFMD.solution k c ε 𝔉 J h M e he ε' hε'
  exact ⟨pts,hadd,hread⟩
end P2MW.S_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_pullback_iff_ell_pos
