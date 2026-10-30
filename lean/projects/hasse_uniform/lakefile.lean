import Lake
open Lake DSL

package hasse_uniform where
  fixedToolchain := true

require fourcorner_paper from "../.."

@[default_target]
lean_lib HasseUniformProject where
  srcDir := "Source"
  roots := #[`HasseUniformCompleteAudit]
  globs := #[
    .one `CompleteSource11,
    .one `HasseRationalSource,
    .one `HasseProjectivePoint,
    .one `HasseAnchorChoice,
    .one `HasseObstructionArithmetic,
    .one `HilbertArithmeticHigh11,
    .one `HilbertOddFormulaHigh11,
    .one `HilbertDyadicFormulaHigh11,
    .one `HilbertWellDefinedHigh11,
    .one `HasseHilbertArithmetic,
    .one `HasseLocalUnits,
    .one `HasseOddSymbol,
    .one `HasseTangentGlobal,
    .one `HasseDyadicSymbol,
    .one `HasseDyadicNonunit,
    .one `HasseDyadicAlgebra,
    .one `HasseDyadicDepthFive,
    .one `HasseDyadicUnitOneNormalization,
    .one `HasseConicTangentParity,
    .one `HasseRationalNormalization,
    .one `HasseGoodUnitRow,
    .one `HasseParameterSupport,
    .one `HasseSignAlgebra,
    .one `HasseInertNormMin,
    .one `HasseInertSupport,
    .one `HasseTwoSymbol,
    .one `HasseConstantCorrection,
    .one `HasseConstantOdd,
    .one `HasseConstantDyadic,
    .one `HasseUnitFifteenNormalization,
    .one `HasseUnitFifteenFactor,
    .one `HasseDyadicUnitFinite,
    .one `HasseDyadicUnitOneResidue,
    .one `HasseDyadicIntegralSign,
    .one `HasseDyadicUnitOneFlip,
    .one `HasseDyadicUnitOneModel,
    .one `HasseDyadicUnitOneRow,
    .one `HasseDyadicUnitFifteenFinite,
    .one `HasseDyadicIntegralTwo,
    .one `HasseDyadicUnitFifteenModel,
    .one `HasseUnitFifteenSign,
    .one `HasseInertParity,
    .one `HasseWR,
    .one `HasseUnitFifteenRow,
    .one `HasseFiniteAssembly,
    .one `HasseFinalDyadic,
    .one `HasseParameterValuations,
    .one `HasseOddSourceRows,
    .one `HasseOddBadModels,
    .one `HassePositiveBInert,
    .one `HassePositiveAEven,
    .one `HasseInertPole,
    .one `HasseEvenPoleModel,
    .one `HasseEvenPole,
    .one `HasseKnownCorrectedRows,
    .one `HasseOddSymbolAlgebra,
    .one `HasseAntiDiagonal,
    .one `HasseTangentUTransfer,
    .one `HasseTangentScaling,
    .one `HassePoleParameters,
    .one `HasseOddPoleCoordinates,
    .one `HasseOddPoleResidues,
    .one `HasseOddPole,
    .one `HassePositiveAOddCoordinates,
    .one `HassePositiveAOdd,
    .one `HasseCorrectedOddProduct,
    .one `HasseUniformNoPoint,
    .one `HasseUniformCompleteAudit
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
