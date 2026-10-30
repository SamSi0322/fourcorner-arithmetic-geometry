import ThetaCoverClassPortable.DGeometricGenus
import ThetaCoverClassPortable.DUniformRiemannRoch
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
import ThetaCoverClassPortable.FMDUnitH1
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 12000000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ActualPicardProperties

/-- Exact all-model genus identification for the actual original D after ANY
QQ-algebra base change. The input RR equation determines its own integer. -/
theorem D_baseChange_RR_genus
    (T : Type) [CommRing T] [Algebra ℚ T]
    (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (.of k) ⟶ Spec (.of T))
    (L : Type) [Field L] [Algebra k L] (M : CurveModel k L)
    (e : M.C ≅ pullback (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T) s)
    (he : e.hom ≫ pullback.snd (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T) s = M.toBase)
    (Kc : Divisor k L) (g' : ℕ)
    (hRR : ∀ D : Divisor k L, (ell D : ℤ) - ell (Kc-D) = Divisor.degree D + 1 - g') : g'=3 := by
  let qT := SmoothProperCurve.specMap ℚ T
  let y := s ≫ qT
  let b := pullbackLeftPullbackSndIso DRationalInputs.toBase qT s
  let e' : M.C ≅ DRationalInputs.XAt y := e ≪≫ b
  have hb : b.hom ≫ pullback.snd DRationalInputs.toBase y =
      pullback.snd (SmoothProperCurve.baseChange ℚ DRationalInputs.toBase T) s :=
    pullbackLeftPullbackSndIso_hom_snd _ _ _
  have he' : e'.hom ≫ DRationalInputs.cAt y = M.toBase := by
    change (e.hom ≫ b.hom) ≫ pullback.snd DRationalInputs.toBase y = _
    rw [Category.assoc,hb,he]
  letI := M.isIntegral
  letI := M.isProper
  letI := M.smooth
  letI := M.functionFieldAlgebra
  letI := DRationalInputs.integral_at y
  letI := (baseToFunctionField (DRationalInputs.cAt y)).toAlgebra
  haveI : IsCurveOver k L := isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    M.toBase M.ffEquiv M.ffEquiv_algebraMap
  haveI : Algebra.EssFiniteType k M.C.functionField := essFiniteType_functionField M.toBase
  haveI : Algebra.EssFiniteType k L := Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.symm.toAlgHom M.ffAlgEquiv.symm.surjective
  obtain ⟨t,ht,hfd,hsep⟩ := IsCurveOver.exists_separating_transcendental (K:=k) (F:=L)
  letI := hfd
  have hc := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  let eNative := ThetaIsoFunctionField.algEquiv M.toBase (DRationalInputs.cAt y) e' he'
  let eAll := M.ffAlgEquiv.trans eNative.symm
  exact (eq_genusFF_of_forall_ell_sub_ell_eq hc hRR).trans
    ((genusFF_eq_of_algEquiv eAll).trans (DRationalInputs.actual_genus_three y))

end FourCorner.ActualPicardProperties
