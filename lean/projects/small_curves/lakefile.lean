import Lake
open Lake DSL
package fourcorner_small_curves where
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`debug.skipKernelTC, false⟩,
    ⟨`maxHeartbeats, (4000000 : Nat)⟩, ⟨`maxSynthPendingDepth, (3 : Nat)⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩]
require fourcorner_elliptic_foundations from "vendor/EllipticFoundations"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"
lean_lib FourCorner where
  srcDir := "source"
  roots := #[]
  globs := #[
    .one `FourCorner.CommonRootSupportDecomposition,
    .one `FourCorner.NineCubicValuation,
    .one `FourCorner.NineFlexGroup,
    .one `FourCorner.NineSmallACoordinates,
    .one `FourCorner.NineSmallALocal,
    .one `FourCorner.NineSmallAPoints,
    .one `FourCorner.NineSmallASignedSupport,
    .one `FourCorner.NineSmallE0,
    .one `FourCorner.NineSmallE0Local,
    .one `FourCorner.NineSmallE0Points,
    .one `FourCorner.NineSmallE1,
    .one `FourCorner.NineSmallE2,
    .one `FourCorner.NineSmallFiniteFive,
    .one `FourCorner.RatIntegralAux,
    .one `FourCorner.RationalSquarefree,
    .one `FourCorner.SquareArea,
    .one `FourCorner.SquarefreePart
  ]
lean_lib OrderedEval where
  srcDir := "source"
lean_lib SignedSquareClasses where
  srcDir := "source"
lean_lib OrderedKummer where
  srcDir := "source"
lean_lib SplitCurveOrdered where
  srcDir := "source"
lean_lib FGCardCore where
  srcDir := "source"
lean_lib FGKummerInterface where
  srcDir := "source"
lean_lib ActualKummerFinite where
  srcDir := "source"
lean_lib SmallReduction where
  srcDir := "source"
lean_lib SmallTorsionBounds where
  srcDir := "source"
lean_lib SmallAComplete where
  srcDir := "source"
lean_lib E0KummerImage where
  srcDir := "source"
lean_lib E0Complete where
  srcDir := "source"
@[default_target]
lean_lib NineSmallCurvesComplete where
  srcDir := "source"
