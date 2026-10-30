import Lake
open Lake DSL

package descent_algebra where
  fixedToolchain := true

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib DescentAlgebra where
  srcDir := "Source"
  roots := #[]
  globs := #[
    .one `FiniteWidePullback,
    .one `Theorems.Thm_CategoryTheory_MorphismProperty_widePullback_base,
    .one `WidePullbackSchemeApplications,
    .one `PairCoactionInvariants,
    .one `FlatTensorKernel,
    .one `IdealFlatDescent,
    .one `IdealTensorDescent,
    .one `AffineIdealDescent,
    .one `Theorems.Thm_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight,
    .one `ModuleConstantRankPresentation,
    .one `ModuleLocalizedRank,
    .one `Theorems.Thm_Module_rankAtStalk_eq_of_forall_localizedModule_equiv,
    .one `Theorems.Thm_Module_finitePresentation_of_rankAtStalk_eq,
    .one `DescentAlgebra,
    .one `DescentAlgebraAudit
  ]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`maxSynthPendingDepth, .ofNat 3⟩]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
