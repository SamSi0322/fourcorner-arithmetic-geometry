import Lake
open Lake DSL

package common_exclusion where
  fixedToolchain := true

require fourcorner_paper from "../.."
require adjacent_genus from "../adjacent_genus"

@[default_target]
lean_lib CommonExclusionProject where
  srcDir := "Source"
  roots := #[`CommonExclusionPackage]
  globs := #[
    .one `CommonLiteralField,
    .one `CommonFieldCoordinates,
    .one `CommonBoundaryCharts,
    .one `CommonRationalPlace,
    .one `CommonActualBoundary,
    .one `CommonRoot37Discriminant,
    .one `CommonRootExclusion,
    .one `RationalPlaceSource07,
    .one `CurveRationalPlace07,
    .one `CommonFourDegree,
    .one `CommonFiveIndependence,
    .one `CommonActualDegree,
    .one `CommonTower,
    .one `CommonFifthDegree,
    .one `CommonGenus17Field,
    .one `CommonGenus17Unramified,
    .one `CommonQuadraticParity,
    .one `CommonFourRamification,
    .one `CommonFourPlaceOrders,
    .one `CommonRamificationSum,
    .one `CommonActualGenus,
    .one `CommonSchemeModel,
    .one `CommonPostPointResidue,
    .one `CommonPointSource,
    .one `CommonConstantMap,
    .one `CommonTensorRank,
    .one `CommonFieldTensorDomain,
    .one `CommonTensorLocalization,
    .one `CommonConstantTensorInjection,
    .one `CommonTensorFlat,
    .one `CommonGeometricField,
    .one `CommonSchemeGeometricIntegral,
    .one `CommonSchemeDifferentials,
    .one `CommonRootFieldComparison,
    .one `CommonConstantTensorFraction,
    .one `CommonTensorCancelLeft,
    .one `CommonConstantFieldComparison,
    .one `CommonPostGeometricGenus,
    .one `CommonPostBoundaryPlaces,
    .one `ProperCurveFieldIsoQ,
    .one `ProjectiveLineCharts,
    .one `ProjectiveLineGeometry,
    .one `ProjectiveLineField,
    .one `NormalizedBaseP1,
    .one `CommonPostFiniteP1,
    .one `CommonPostModelBoundary,
    .one `CommonExclusion,
    .one `CommonExclusionPaper,
    .one `FamilySixMatrix08,
    .one `FamilySixKernel08,
    .one `CommonFamilyRank,
    .one `FamilyConstituents,
    .one `FourRootLift08,
    .one `RealTranscendentalSource08,
    .one `RealFieldEmbedding08,
    .one `ProperCommonExclusion07,
    .one `ActualRealPoint08,
    .one `CommonInfinite,
    .one `CommonExclusionPackage
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
