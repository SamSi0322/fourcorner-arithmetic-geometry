import Lake
open Lake DSL

package cs15569 where
  fixedToolchain := true

require fourcorner_paper from "../.."
require fourcorner_elliptic_foundations from "../small_curves/vendor/EllipticFoundations"

@[default_target]
lean_lib Cs15569Project where
  srcDir := "Source"
  roots := #[`Cs15569Audit]
  globs := #[
    .one `RationalSupport15569,
    .one `HSupport15569,
    .one `Cs15569DyadicResidues,
    .one `Cs15569DyadicUnit,
    .one `Cs15569Finite,
    .one `RationalCosets15569,
    .one `Cs15569DyadicSplitting,
    .one `Cs15569DyadicGeneration,
    .one `Cs15569RationalReduction,
    .one `Cs15569SourceParity,
    .one `Cs15569Group,
    .one `Cs15569Reduction113,
    .one `ActualBranch15569,
    .one `Cs15569SourceTorsion,
    .one `Cs15569FiniteSource113,
    .one `Cs15569DyadicDepth,
    .one `Cs15569DyadicCharacterEight,
    .one `Cs15569DyadicSquareEight,
    .one `ThreeRootDisks15569,
    .one `Cs15569ThreeReduction,
    .one `Cs15569DyadicOddDepth,
    .one `Cs15569ActualSourceImage113,
    .one `Cs15569ReturnExclusion113,
    .one `SourceLayer17,
    .one `Cs15569Complete,
    .one `Cs15569Audit,
    .one `CS15569Support.NineCubicValuation,
    .one `CS15569Support.NineSmallASignedSupport,
    .one `GroupInterface,
    .one `OrderedEval,
    .one `SignedSquareClasses,
    .one `OrderedKummer,
    .one `KummerBridge,
    .one `DyadicBridge,
    .one `CSFoundation.CommonSourceDyadicChart,
    .one `LocalKummerSelection,
    .one `ActualSourceCoset,
    .one `CSFoundation.CommonSourceDyadicReturn,
    .one `CSFoundation.CommonSourceDyadicExcluded,
    .one `CSFoundation.CommonSourceDyadicOrders,
    .one `ActualTorsionOrders,
    .one `ActualSourceDepth,
    .one `ActualSurvivingOrders,
    .one `CSFoundation.CommonSourceBeta,
    .one `ActualPairData,
    .one `FieldGroup,
    .one `RationalPrimeValuation,
    .one `ReductionBridge,
    .one `CSFoundation.CommonSourceOddLocalResidue,
    .one `FormalLogOdd,
    .one `IntegralScaledLog,
    .one `FormalLogEvaluation,
    .one `LogModFourPrecision,
    .one `CSLogSupport.CommonSourceDyadicResidue,
    .one `RationalFormalDepth,
    .one `DyadicCharacter,
    .one `ActualDyadicCharacter15,
    .one `ActualCharacterSign,
    .one `ActualLogParameter,
    .one `CSFoundation.CommonSourceOddLocal,
    .one `CSFoundation.CommonSourceOddLocalDisks,
    .one `CSFoundation.CommonSourceOddLocalAssembly,
    .one `OddEvenMismatch,
    .one `ActualPairPaperAdapter
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
