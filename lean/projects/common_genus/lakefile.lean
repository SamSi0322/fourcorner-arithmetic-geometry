import Lake
open Lake DSL

package common_genus where
  fixedToolchain := true

require common_exclusion from "../common_exclusion"

@[default_target]
lean_lib CommonGenusProject where
  srcDir := "Source"
  roots := #[`CommonGenusPackage]
  globs := #[
    .one `CommonPostRamification,
    .one `NormalizationPlaceRestriction,
    .one `NormalizationPointRestriction,
    .one `NormalizedModelPointRestriction,
    .one `CommonPostBranchFibres,
    .one `CommonPostBranchValues,
    .one `NormalizationGenericPoint,
    .one `FractionGenericStalk,
    .one `GenericStalkField,
    .one `CommonPostGenericEll,
    .one `CommonPostStalkFields,
    .one `CommonPostEllDegree,
    .one `CommonGenusBoundaryFull,
    .one `CommonGenusPackage
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
