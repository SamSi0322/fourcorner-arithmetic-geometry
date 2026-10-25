import Lake
open Lake DSL

package common_genus17 where
  fixedToolchain := true

require common_genus from "../common_genus"

@[default_target]
lean_lib CommonGenus17Project where
  srcDir := "Source"
  roots := #[`Genus17Package]
  globs := #[
    .one `Genus17Model,
    .one `Genus17Cover,
    .one `CanonicalGenericField,
    .one `Genus17GenericCover,
    .one `Genus17Coordinates,
    .one `Genus17FieldGenus,
    .one `Genus17PointMap,
    .one `FiveSquareDegree,
    .one `Genus17Generators,
    .one `FiniteTensorGenerators,
    .one `Genus17TensorComparison,
    .one `Genus17GeometricField,
    .one `Genus17ConstantFieldComparison,
    .one `Genus17GeometricModel,
    .one `Genus17GeometricGenus,
    .one `Genus17GeometryStatement,
    .one `Genus17ResidueSeparable,
    .one `Genus17ValuativeUnramified,
    .one `Genus17GenericSeparable,
    .one `Genus17GeometryComplete,
    .one `Genus17Support,
    .one `RationalPlaceSourceAnyAlgebra,
    .one `UnitDiscriminantClosure,
    .one `QuadraticDiscriminant,
    .one `Genus17PowerBasis,
    .one `QuadraticOrder,
    .one `QuadraticOrderEvaluation,
    .one `QuadraticClosureEvaluation,
    .one `RationalPlacePoint,
    .one `QuadraticPlaceExtension,
    .one `Genus17PlaceLift,
    .one `RationalCoordinateLift,
    .one `Genus17ActualLift,
    .one `Genus17TwistsPositive,
    .one `Genus17Full,
    .one `Genus17PointSupport,
    .one `Genus17Package
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
