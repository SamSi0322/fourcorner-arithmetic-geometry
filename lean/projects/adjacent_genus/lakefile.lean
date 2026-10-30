import Lake
open Lake DSL

package adjacent_genus where
  fixedToolchain := true

require opposite_genus from "../opposite_genus"

@[default_target]
lean_lib AdjacentGenus where
  srcDir := "Source"
  roots := #[`AdjacentGenus]
  globs := #[
    .one `NormalizationCoefficientMap,
    .one `GenericNormalizedGluing,
    .one `NormalizationCoverMap,
    .one `FiniteNormalizationChartMaps,
    .one `FiniteNormalizationCover,
    .one `NormalizationCoverField,
    .one `ProperCurveExtension,
    .one `AdjacentPostTwoChartCover,
    .one `AdjacentPostScalarSmooth,
    .one `AdjacentPostAffineSmooth,
    .one `AdjacentPostModelSource,
    .one `AdjacentPostSourceMap,
    .one `AdjacentPostNormalizedCharts,
    .one `NormalizedModelCover,
    .one `AdjacentPostEndpoint,
    .one `AdjacentNormalizationCover,
    .one `AdjacentGenus
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
