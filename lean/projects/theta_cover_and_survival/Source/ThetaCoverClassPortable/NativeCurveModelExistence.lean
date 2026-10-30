import ThetaCoverClassPortable.geometry.SchemeModelFiniteExtension
import ThetaCoverClassPortable.SmoothCurveFieldIso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
universe u
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.NativeCurveModelExistence

/-- A genuine model of the NATIVE function field of the specified smooth
proper integral curve over ANY characteristic-zero field. Both the model
and the actual over-base/generic isomorphism are constructed. -/
theorem exists_model {K : Type u} [Field K] [CharZero K] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of K)) [IsIntegral X] [SmoothOfRelativeDimension 1 c] [IsProper c] :
    letI := SmoothCurveExtension.fieldAlgebra c
    ∃ M : CurveModel K X.functionField, ∃ i : X ≅ M.C,
      i.hom ≫ M.toBase=c ∧
      X.fromSpecStalk (genericPoint X) ≫ i.hom=
        Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
          M.C.fromSpecStalk (genericPoint M.C) := by
  letI := SmoothCurveExtension.fieldAlgebra c
  letI : IsCurveOver K X.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c (RingEquiv.refl _) (fun _ => rfl)
  letI : Algebra.EssFiniteType K X.functionField := essFiniteType_functionField c
  obtain ⟨t,ht,hfd,hsep⟩ := IsCurveOver.exists_separating_transcendental (K:=K) (F:=X.functionField)
  letI := hfd
  have ht0 : t≠0 := by intro h;rw [h] at ht;exact ht isAlgebraic_zero
  letI : Fact (t≠0) := ⟨ht0⟩
  letI : FiniteDimensional (IntermediateField.adjoin K ({t⁻¹} : Set X.functionField)) X.functionField := by
    rw [CurveModel.adjoin_simple_inv_eq]
    infer_instance
  let M : CurveModel K X.functionField := CurveModel.ofGenerator K t ht
  letI := M.isIntegral
  letI := M.isProper
  letI := M.smooth
  letI := M.functionFieldAlgebra
  let e : M.C.functionField ≃ₐ[K] X.functionField := M.ffAlgEquiv.symm
  obtain ⟨i,hi,hg⟩ := SmoothCurveExtension.iso_of_functionField_algEquiv c M.toBase e
  have he : e.toRingEquiv.toRingHom=M.ffEquiv.symm.toRingHom := by ext x;rfl
  rw [he] at hg
  exact ⟨M,i,hi,hg⟩

#print axioms exists_model
end FourCorner.NativeCurveModelExistence
