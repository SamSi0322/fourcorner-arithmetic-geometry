import ThetaCoverClassPortable.ThetaUniformGeometricGenus
import ThetaCoverClassPortable.RiemannRochWithGenusFF
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaUniformRiemannRoch
open ThetaLiteralModels ThetaUniformGeometricGenus

/-- For EVERY genuine curve model of EVERY actual algebraically closed
geometric fibre of original C/Q, the uniform RR equation has genus FIVE.
The native scheme/function-field comparisons, genus and RR existence are
proved; neither RR nor a genus identification is a caller premise. -/
theorem rr_five {K L : Type} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    (y : Spec (.of K) ⟶ Spec (.of ℚ)) (M : CurveModel K L)
    (e : M.C ≅ XAt y) (he : e.hom ≫ cAt y=M.toBase) :
    ∃ Kc : Divisor K L, ∀ D : Divisor K L,
      (ell D:ℤ)-ell (Kc-D)=Divisor.degree D+1-5 := by
  letI := M.isIntegral
  letI := M.isProper
  letI := M.smooth
  letI := M.functionFieldAlgebra
  letI := integral_at y
  letI := (baseToFunctionField (cAt y)).toAlgebra
  haveI : IsCurveOver K L := isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    M.toBase M.ffEquiv M.ffEquiv_algebraMap
  haveI : Algebra.EssFiniteType K M.C.functionField := essFiniteType_functionField M.toBase
  haveI : Algebra.EssFiniteType K L :=
    Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.symm.toAlgHom M.ffAlgEquiv.symm.surjective
  let eNative := ThetaIsoFunctionField.algEquiv M.toBase (cAt y) e he
  let eAll := M.ffAlgEquiv.trans eNative.symm
  have hgenus : genusFF K L=5 :=
    (genusFF_eq_of_algEquiv eAll).trans (actual_genus_five y)
  obtain ⟨Kc,hRR⟩ := RiemannRochWithGenusFF.exists_rr (K:=K) (F:=L)
  rw [hgenus] at hRR
  exact ⟨Kc,hRR⟩

#print axioms rr_five
end FourCorner.ThetaUniformRiemannRoch
