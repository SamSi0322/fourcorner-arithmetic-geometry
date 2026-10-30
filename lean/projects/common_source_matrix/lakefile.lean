import Lake
open Lake DSL

package common_source_matrix where
  fixedToolchain := true

require common_source from "../common_source"

@[default_target]
lean_lib CommonSourceMatrixProject where
  srcDir := "Source"
  roots := #[`CommonSourceMatrixPackage]
  globs := #[
    .one `FormalLogOdd,
    .one `IntegralScaledLog,
    .one `FormalLogEvaluation,
    .one `LogModFourPrecision,
    .one `CSLogSupport.CommonSourceDyadicResidue,
    .one `RationalFormalDepth,
    .one `DyadicCharacter,
    .one `ActualDyadicCharacter15,
    .one `ActualCharacterSign,
    .one `ActualLogParameter,
    .one `ActualLogCharacter,
    .one `FormalCurveNaturality,
    .one `ShortSeriesCore,
    .one `ChordRestriction,
    .one `ShortInvariantDifferential,
    .one `ShortLogIntegrand,
    .one `DerivationPullback,
    .one `LiteralFormalCurve,
    .one `PaperLogIdentification,
    .one `CoordinateRingPullback,
    .one `ActualDyadicSourceSign,
    .one `PaperCommonSourceCriterion,
    .one `PaperCommonSourceRaw,
    .one `CommonSourceMatrixFull,
    .one `CommonSourceMatrixPackage
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
