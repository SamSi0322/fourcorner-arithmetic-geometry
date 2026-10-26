import Lake
open Lake DSL

package theta_quotient where
  fixedToolchain := true

require critical_elliptic from "../critical_elliptic"

@[default_target]
lean_lib ThetaQuotientProject where
  srcDir := "Source"
  roots := #[`ThetaQuotientAudit]
  globs := #[
    .one `ThetaAmbientChart,
    .one `ThetaQuotientChart,
    .one `ThetaProjectiveModel,
    .one `ThetaProjectiveCoordinates,
    .one `ThetaLiteralModels,
    .one `ThetaMvPolynomialPolynomial,
    .one `ThetaPolynomialFunext,
    .one `ThetaOppositeComparison,
    .one `ThetaModelBase,
    .one `ThetaSourceSmooth,
    .one `ThetaProjEquality,
    .one `ThetaSourceComparison,
    .one `ThetaProjMap,
    .one `ThetaProjection,
    .one `ThetaInvolution,
    .one `ThetaHomogeneousSign,
    .one `ThetaQuadraticKernel,
    .one `ThetaPairPresentation,
    .one `ThetaPairInvariants,
    .one `ThetaActualPoints,
    .one `ThetaPointAPI,
    .one `ThetaHomogeneousEvaluation,
    .one `ThetaBoundary,
    .one `ThetaOriginImage,
    .one `ThetaQuotientCharts,
    .one `ThetaChartAlgebras,
    .one `ThetaSourcePresentation,
    .one `ThetaSourcePairData,
    .one `ThetaProjectionChartMap,
    .one `ThetaInvolutionChart,
    .one `ThetaPairBaseChange,
    .one `ThetaPairDescent,
    .one `ThetaChartFiniteEtale,
    .one `ThetaProjectionFiniteEtale,
    .one `ThetaStdRingFlatRank,
    .one `ThetaPairRank,
    .one `ThetaStdModuleFinitePresentation,
    .one `ThetaStdSchemeFlatRank,
    .one `ThetaProjectionDegree,
    .one `ThetaDeckInvolution,
    .one `ThetaPairInvariantEquiv,
    .one `ThetaPairGalois,
    .one `ThetaActualQuotient,
    .one `ThetaIsoFunctionField,
    .one `ThetaSourceGenus,
    .one `ThetaTargetSmooth,
    .one `ThetaQuotient,
    .one `ThetaQuotientAudit
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
