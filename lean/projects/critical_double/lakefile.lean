import Lake
open Lake DSL

package critical_double where
  fixedToolchain := true

require critical_refined from "../critical_refined"

@[default_target]
lean_lib CriticalDoubleProject where
  srcDir := "Source"
  roots := #[`CriticalDoubleFullAudit]
  globs := #[
    .one `CriticalDoubleGeometricGenus,
    .one `CriticalDoubleSchemeMap,
    .one `CriticalDoubleModel,
    .one `CriticalOriginalFieldCoordinates,
    .one `CriticalDoubleOriginalMap,
    .one `CriticalNativeGeometricGenus,
    .one `CriticalCoverGenericField,
    .one `CriticalCoverGenericSeparable,
    .one `NativeUnramifiedFinite,
    .one `SmoothProperClosedPointPlaces,
    .one `SchemePointStalkEvaluation,
    .one `SmoothProperRationalPointPlaces,
    .one `SmoothProperPointPlaceTransport,
    .one `AffineChartStalkFunctions,
    .one `SmoothProperPlaceNaturality,
    .one `PlaceDifferentUnramified,
    .one `AllPointStalkUnramified,
    .one `AllPointSchemeProperties,
    .one `AffineChartPlaceEvaluation,
    .one `RestrictionUnramifiedTransport,
    .one `CriticalCoverNativeProperties,
    .one `AllPointFlat,
    .one `CriticalCoverNativeEtale,
    .one `CriticalSchemePointPlaces,
    .one `CriticalDoubleGeometry,
    .one `CriticalDoubleFullGeometry,
    .one `CriticalNormalizationDiagram,
    .one `CriticalPointTransportValuation,
    .one `BundledPointPlaceNaturality,
    .one `AbstractPresentationPlaceTransport,
    .one `CriticalPointNaturality,
    .one `CriticalBoundaryRootCounts,
    .one `CriticalBoundaryUnits,
    .one `CriticalBoundaryFibre,
    .one `CriticalActualBoundaryCount,
    .one `CriticalOffBoundaryUnit,
    .one `CriticalOffBoundaryFibre,
    .one `CriticalFiniteRationalPlaces,
    .one `FiniteFibreCounting,
    .one `CriticalGlobalFibreCount,
    .one `CriticalSchemeCount,
    .one `FixedAffinePointEvaluation,
    .one `CriticalFixedPlaceEvaluation,
    .one `CriticalSchemeBoundary,
    .one `ChartSectionGeneric,
    .one `CriticalChartGenericFunctions,
    .one `CriticalFixedChartCoordinates,
    .one `CriticalChartResidueEvaluation,
    .one `CriticalNormalizedChartPoint,
    .one `CriticalAllPointResiduePresentation,
    .one `CriticalLiteralSchemeCharacter,
    .one `CriticalLiteralCount,
    .one `CriticalSchemeBoundaryCount,
    .one `CriticalDoubleFull,
    .one `CriticalDoubleFullAudit
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
