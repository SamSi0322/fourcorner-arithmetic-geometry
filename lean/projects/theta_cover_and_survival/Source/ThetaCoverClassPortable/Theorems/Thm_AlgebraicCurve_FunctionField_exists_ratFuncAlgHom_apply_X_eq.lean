import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq
set_option autoImplicit false
namespace AlgebraicCurve.FunctionField
theorem exists_ratFuncAlgHom_apply_X_eq {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    {g : F} (hg : g ∉ Set.range (algebraMap K F)) : ∃ φ : RatFunc K →ₐ[K] F, φ RatFunc.X=g :=
  P2MW.S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq.solution hg
end AlgebraicCurve.FunctionField
#print axioms AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq
