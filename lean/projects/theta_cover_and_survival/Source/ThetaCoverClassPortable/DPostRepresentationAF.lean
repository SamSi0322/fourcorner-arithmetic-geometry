import ThetaCoverClassPortable.DPostRepresentationTheta
import ThetaCoverClassPortable.ActualPicardLocallyFiniteType
import ThetaCoverClassPortable.ActualThetaCubeFBSQQ
import ThetaCoverClassPortable.ActualFBSFlatBase
import ThetaCoverClassPortable.ActualFiniteBaseFlat
import ThetaCoverClassPortable.ActualProjAffineQQ
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_fst_thetaBundle_iso_baseChange
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
namespace FourCorner.ActualPicardProperties

private def tensorPowerCongr {X : Scheme} {L L' : X.Modules} (e : L ≅ L') :
    ∀ n : ℕ, L.tensorPow n ≅ L'.tensorPow n
  | 0 => Iso.refl _
  | n+1 => tensorIso (tensorPowerCongr e n) e

/-- The actual represented Picard of the SAME D_T over a finite reduced
rational algebra has the affine-neighbourhood property. Global generation is
constructed by true flat H0 base change, without a Serre or H1 hypothesis. -/
theorem D_baseChange_exists_isAffineOpen
    (T : Type) [CommRing T] [Algebra ℚ T] [Module.Finite ℚ T] [_root_.IsReduced T]
    (D : RelativePic0Designation T (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T))
    (h : RepresentsRelSubPic (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T)
      (SmoothProperCurve.sectionBaseChange T DRationalInputs.OD)
      (algEquivZeroCut (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T)
        (SmoothProperCurve.sectionBaseChange T DRationalInputs.OD)) D)
    :
    ∀ S : Finset D.P, ∃ U : D.P.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := by
  haveI : IsNoetherianRing T := IsNoetherianRing.of_finite ℚ T
  let c := SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T
  let ε := SmoothProperCurve.sectionBaseChange T DRationalInputs.OD
  letI := DRationalInputs.proper
  letI := DRationalInputs.smooth
  letI := DRationalInputs.geometricallyIntegral
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : IsProper c := inferInstance
  haveI : SmoothOfRelativeDimension 1 c := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : GeometricallyIntegral c := inferInstance
  haveI : LocallyOfFiniteType D.toBase := FourCorner.ActualPicardLocallyFiniteType.solution T c ε
    ((DRationalInputs.actual_finiteMapData 0).baseChange T) D h
  obtain ⟨hsm,hpr,hgc,hsep⟩ := D_baseChange_postrep_properties T D h
  letI := hsm
  letI := hpr
  letI := hgc
  letI := hsep
  have hF : ∀ m0 : ℕ, ∃ F : SmoothProperCurve.FiniteMapData c ε, m0 ≤ F.m := by
    intro m0
    obtain ⟨F,hF,_⟩ := DRationalInputs.actual_unbounded_finiteMapData_baseChange T m0
    exact ⟨F,hF⟩
  let F0 := (DRationalInputs.actual_finiteMapData 0).baseChange T
  have hg : AllModelRRGenus c 3 := D_baseChange_RR_genus T
  let L := thetaBundle c ε D.toBase h.poincare 6 4
  have hL : Scheme.Modules.IsInvertible L := D_baseChange_theta_invertible T D h
  have hOrigFib := P2MW.ActualFibrePoincareTwistQQ.solution T c ε (algebraMap ℚ T) F0 D h 3 hg 6 (by omega)
  have hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra T K], ∃ n : ℕ,
      Scheme.Modules.FiniteBySections
        ((Scheme.Modules.pullback (pullback.fst D.toBase (SmoothProperCurve.specMap T K))).obj (L.tensorPow n))
        (pullback.snd D.toBase (SmoothProperCurve.specMap T K)) := by
    intro K _ _ _
    letI : Algebra ℚ K := ((algebraMap T K).comp (algebraMap ℚ T)).toAlgebra
    obtain ⟨hK,⟨eP⟩⟩ := AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange T c ε D h K
    have hFK : ∀ m0 : ℕ, ∃ F : SmoothProperCurve.FiniteMapData
        (SmoothProperCurve.baseChange T c K) (SmoothProperCurve.sectionBaseChange K ε), m0 ≤ F.m := by
      intro m0
      obtain ⟨F,hFm⟩ := hF m0
      exact ⟨F.baseChange K,hFm⟩
    have hgK := AllModelRRGenus.baseChange hg K
    have hCube := P2MW.ActualThetaCubeFBSQQ.solution K (SmoothProperCurve.baseChange T c K)
      (SmoothProperCurve.sectionBaseChange K ε) hFK (D.baseChange K) hK
      inferInstance inferInstance inferInstance 3 hgK (by omega) 6 (by omega)
    obtain ⟨eΘ⟩ := AlgebraicGeometry.RelPicard.nonempty_pullback_fst_thetaBundle_iso_baseChange
      T c ε hF D.toBase h.poincare 6 4 hOrigFib K hK.poincare eP
    obtain ⟨ePow⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso
      (pullback.fst D.toBase (SmoothProperCurve.specMap T K)) L 3
    refine ⟨3,Scheme.Modules.FiniteBySections.of_iso ?_ hCube⟩
    exact (ePow ≪≫ tensorPowerCongr eΘ 3).symm
  have hflat : ∀ (K : Type) [Field K] [Algebra T K], Module.Flat T K := by
    intro K _ _
    exact finite_reduced_QQ_module_flat T K
  obtain ⟨n,N,𝔓,hfin⟩ := P2MW.ActualFBSFlatBase.solution T D.toBase L hL hflat hfib
  letI := hfin
  exact exists_isAffineOpen_forall_mem_of_isAffineHom_standardProj_QQ T N 𝔓.toProj

#print axioms D_baseChange_exists_isAffineOpen
end FourCorner.ActualPicardProperties
