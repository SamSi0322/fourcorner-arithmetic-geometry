import Lake
open Lake DSL

package original_cover where
  fixedToolchain := true

require critical_prime from "../critical_prime"
require fourcorner_paper from "../.."

@[default_target]
lean_lib OriginalCoverProject where
  srcDir := "Source"
  roots := #[`OriginalCoverAudit]
  globs := #[
    .one `OriginalDiagonalPresentation,
    .one `OriginalTowerPresentation,
    .one `OriginalRadicandIndependence,
    .one `FourRadicalGenericField,
    .one `OriginalIntegralDomain,
    .one `OriginalDeckObstruction,
    .one `OriginalQuadraticDegree,
    .one `OrderedSourceRadicands,
    .one `OrderedSourceFunctionField,
    .one `OrderedSourceRationalAlgebra,
    .one `OrderedSourceCoordinates,
    .one `OrderedSourceInverse,
    .one `OrderedSourceGeneration,
    .one `OrderedSourceDominance,
    .one `OrderedSourceFieldEmbedding,
    .one `RationalFieldGeneration,
    .one `OriginalCoverExact,
    .one `OriginalCoverAudit
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
