import Lake
open Lake DSL

package common_source where
  fixedToolchain := true

require fourcorner_paper from "../.."
require fourcorner_small_curves from "../small_curves"

@[default_target]
lean_lib CommonSourceProject where
  srcDir := "Source"
  roots := #[`CommonSourcePackage]
  globs := #[
    .one `GroupInterface,
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
    .one `Slot14.OddProbe,
    .one `CSFoundation.CommonSourceOddLocal,
    .one `OddKummerSpecialization,
    .one `ActualCyclicLabels,
    .one `CSFoundation.CommonSourceOddLocalResidue,
    .one `OddTranslationsReplay,
    .one `OddWrongReturn,
    .one `CSFoundation.CommonSourceOddLocalDisks,
    .one `CSFoundation.CommonSourceOddLocalAssembly,
    .one `OddEvenMismatch,
    .one `ActualOddReturnBridge,
    .one `ActualCyclicOddRow,
    .one `ActualNeutralOddRow,
    .one `ActualPairPaperAdapter,
    .one `OddRowFull,
    .one `CommonSourcePackage
  ]
  moreLeanArgs := #["-Ddebug.skipKernelTC=false"]
