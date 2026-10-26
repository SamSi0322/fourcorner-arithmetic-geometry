import Lake
open Lake DSL

package critical_refined where
  fixedToolchain := true

require critical_prime from "../critical_prime"

@[default_target]
lean_lib CriticalRefinedProject where
  srcDir := "Source"
  roots := #[`RefinedFiniteAudit]
  globs := #[
    .one `RationalPlaceEvaluationUnique,
    .one `RationalPlaceFibreHom,
    .one `CriticalRationalFibres,
    .one `QuadraticUnitIntegralClosure,
    .one `QuadraticUnitResidueAlgebra,
    .one `QuadraticUnitRootHom,
    .one `QuadraticRationalPlaceFibre,
    .one `RationalPlaceTower,
    .one `RationalLineEvaluation,
    .one `QuadraticLinearNorm,
    .one `TwoRootProductObstruction,
    .one `CriticalProductNonsquare,
    .one `CriticalProductValuation,
    .one `CriticalProductOrders,
    .one `CriticalLiteralDouble,
    .one `CriticalBoundaryResidues,
    .one `CriticalBoundaryTower,
    .one `CriticalBoundaryFibres,
    .one `CriticalBoundaryPlaceClassification,
    .one `CriticalBoundaryEight,
    .one `RefinedSupport.CriticalRefinedWave27,
    .one `RefinedFiniteSource,
    .one `CriticalDoubleCM,
    .one `CriticalProductSquareclass,
    .one `CriticalOriginalFieldEquiv,
    .one `CriticalDoubleFieldMap,
    .one `CriticalDoubleProductBridge,
    .one `CriticalEllipticBaseChange,
    .one `CriticalDoubleNonsquare,
    .one `CriticalEllipticGenerators,
    .one `CriticalCMGeneration,
    .one `CriticalQuadraticLift,
    .one `CriticalDoubleFieldIso,
    .one `CriticalDoublePointCount,
    .one `CriticalRefinedNumerics,
    .one `RefinedCoverHasse,
    .one `RefinedBadCover,
    .one `CriticalProjectiveCharacter,
    .one `CriticalProjectiveResidues,
    .one `CriticalProjectiveBoundary,
    .one `CriticalNonsquareIUnits,
    .one `CriticalBoundaryCharacter,
    .one `RefinedFiniteExistence,
    .one `RefinedPadicSquares,
    .one `RefinedProductSquares,
    .one `RefinedSignedLocalData,
    .one `RefinedSignedFamily,
    .one `RefinedPadicConverse,
    .one `RefinedPaperInterfaces,
    .one `CriticalRefinedFull,
    .one `RefinedFiniteAudit
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
