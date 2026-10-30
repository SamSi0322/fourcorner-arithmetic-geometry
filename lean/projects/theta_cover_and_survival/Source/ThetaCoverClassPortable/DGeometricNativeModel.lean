import ThetaCoverClassPortable.DBaseChangeFields
import ThetaCoverClassPortable.NativeCurveModelExistence
import ThetaCoverClassPortable.NativeCurveGlobalConstants

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
namespace FourCorner.DRationalInputs

/-- Every actual field-valued base change has a native field model and a
proved over-base scheme iso. Characteristic zero comes from t, internally. -/
theorem actual_geometric_native_model {K : Type} [Field K]
    (t : Spec (.of K) ⟶ Spec (.of ℚ)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L)
      (M : CurveModel K L) (e : M.C ≅ XAt t), e.hom ≫ cAt t = M.toBase := by
  letI := charZero_at t
  letI := integral_at t
  letI := smooth_at t
  letI := proper_at t
  letI := SmoothCurveExtension.fieldAlgebra (cAt t)
  obtain ⟨M,i,hi,hg⟩ := NativeCurveModelExistence.exists_model (cAt t)
  refine ⟨(XAt t).functionField,inferInstance,inferInstance,M,i.symm,?_⟩
  change i.inv ≫ cAt t = M.toBase
  have hh := congrArg (fun q : XAt t ⟶ Spec (.of K) => i.inv ≫ q) hi
  simpa only [← Category.assoc,Iso.inv_hom_id,Category.id_comp] using hh.symm

/-- Actual global functions of original D/QQ equal the original rational field. -/
theorem actual_global_sections_bijective :
    letI := integral
    letI := Scheme.TwoAffineOpenCover.algebraOfHom toBase ⊤
    Function.Bijective (algebraMap ℚ Γ(curve,⊤)) := by
  letI := integral
  letI := smooth
  letI := proper
  exact NativeCurveGlobalConstants.global_sections_bijective toBase constantsAreBase

/-- Same constant/global-function comparison on EVERY actual field base change. -/
theorem actual_global_sections_bijective_at {K : Type} [Field K]
    (t : Spec (.of K) ⟶ Spec (.of ℚ)) :
    letI := integral_at t
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (cAt t) ⊤
    Function.Bijective (algebraMap K Γ(XAt t,⊤)) := by
  letI := integral_at t
  letI := smooth_at t
  letI := proper_at t
  exact NativeCurveGlobalConstants.global_sections_bijective (cAt t) (constantsAreBase_at t)

end FourCorner.DRationalInputs
