import Lake
open Lake DSL

package critical_elliptic where
  fixedToolchain := true

require opposite_genus from "../opposite_genus"

@[default_target]
lean_lib CriticalEllipticProject where
  srcDir := "Source"
  roots := #[`CriticalEllipticPackage]
  globs := #[
    .one `CriticalProj23,
    .one `CriticalElliptic23,
    .one `CriticalProjCoordinates23,
    .one `CriticalAffineGeometry,
    .one `CriticalSquareclasses,
    .one `CriticalAffineTower,
    .one `CriticalAffineDomain,
    .one `CriticalAmbientChart,
    .one `CriticalQuotientChart,
    .one `CriticalCharts23,
    .one `CriticalProper23,
    .one `CriticalStandardCharts,
    .one `CriticalSecondChart,
    .one `CriticalSchemePoints23,
    .one `CriticalTwoChartCover,
    .one `CriticalProjectiveIntegral,
    .one `CriticalScalarGeometry,
    .one `CriticalChartJacobian,
    .one `CriticalChartSmooth,
    .one `CriticalChartBase,
    .one `CriticalProjectiveSmooth,
    .one `SmoothCurveValuation,
    .one `SmoothCurveGenericExtension,
    .one `SmoothCurveGenericIso,
    .one `SmoothCurveFieldIso,
    .one `AffineGenericStalk,
    .one `CriticalProjectiveField,
    .one `CriticalConicParameter,
    .one `CriticalQuarticCubic,
    .one `CriticalDirectQuartic,
    .one `CriticalDirectMap,
    .one `CriticalMapTranscendence,
    .one `CriticalEllipticField,
    .one `IntegralEvaluationInjection,
    .one `CriticalEllipticEvaluation,
    .one `CriticalFieldEquivalence,
    .one `CriticalFieldCoordinates,
    .one `FractionFieldGenerators,
    .one `CriticalAffineFieldBridge,
    .one `CriticalMapNaturality,
    .one `CriticalFieldInverse,
    .one `CriticalNativeFieldIso,
    .one `CriticalNativeFieldCoordinates,
    .one `EllipticQuarticModel,
    .one `EllipticQuarticCover,
    .one `EllipticQuarticAffine,
    .one `EllipticQuarticAffineIso,
    .one `EllipticInfinityAffine,
    .one `EllipticQuarticChartBase,
    .one `EllipticQuarticPoint,
    .one `EllipticQuarticIntegral,
    .one `EllipticQuarticFunctionField,
    .one `EllipticQuarticChartSmooth,
    .one `EllipticQuarticSmooth,
    .one `CriticalSchemeIso,
    .one `CriticalAffineBaseChange,
    .one `AffineChartSections,
    .one `CriticalGeometricIntegral,
    .one `CriticalGeometricConnected,
    .one `CriticalExtensionPoints,
    .one `CriticalHomogeneousEvaluation,
    .one `CriticalBoundaryChart,
    .one `CriticalSignPoints,
    .one `CriticalBoundaryClassification,
    .one `CriticalBoundaryCardinality,
    .one `CriticalEllipticFull,
    .one `CriticalEllipticPackage
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
