import Lake
open Lake DSL

package critical_prime where
  fixedToolchain := true

require common_finite_places from "../common_finite_places"
require critical_elliptic from "../critical_elliptic"
require fourcorner_paper from "../.."

@[default_target]
lean_lib CriticalPrimeProject where
  srcDir := "Source"
  roots := #[`CriticalPrimeFullAudit]
  globs := #[
    .one `CrtSupport.CriticalBasicWave24,
    .one `CrtSupport.CriticalBasicLiftWave24,
    .one `CrtSupport.CriticalCRTWave25,
    .one `CrtSupport.CriticalCRTPersistenceWave25,
    .one `CrtSupport.CriticalCongruenceWave24,
    .one `CrtSupport.CriticalCRTAssemblyWave25,
    .one `CrtSupport.CriticalBasicFamilyWave24,
    .one `CriticalCRTInterfaces,
    .one `CriticalRadicalField,
    .one `FractionTensorDomain,
    .one `CriticalFieldConstants,
    .one `CriticalTensorLocalization,
    .one `CriticalConstantFieldComparison,
    .one `CriticalTwoRamification,
    .one `CriticalBranchPlaces,
    .one `CriticalActualRamification,
    .one `CriticalRamificationSum,
    .one `CriticalGeometricGenus,
    .one `CriticalFiniteGenus,
    .one `CriticalFiberBounds,
    .one `CriticalBadCover,
    .one `RationalLinePlaceImage,
    .one `CriticalBadUnits,
    .one `CriticalBadPlaces,
    .one `CriticalHasseNumerics,
    .one `CriticalGoodPlacePattern,
    .one `CriticalCRTPrimeBridge,
    .one `CriticalCRTCompletion,
    .one `PadicUnitNormalization,
    .one `PrimitivePadicCoordinates,
    .one `CriticalNormalizedRadii,
    .one `CriticalResiduePatternData,
    .one `CriticalPadicReverse,
    .one `CriticalOriginalPadicReverse,
    .one `CriticalPaperReverse,
    .one `CriticalBasicFull,
    .one `CriticalPrimeFullAudit
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
