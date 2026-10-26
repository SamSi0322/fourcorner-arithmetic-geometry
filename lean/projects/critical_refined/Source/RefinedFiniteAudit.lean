import CriticalRefinedFull
#check @FourCorner.RefinedFiniteSource.from_good_cover
#check @FourCorner.RefinedCoverHasse.hasse_bound
#check @FourCorner.RefinedBadCover.exists_good_cover_large
#check @FourCorner.RefinedFiniteExistence.allowed_refined_pattern
#check @FourCorner.CriticalRefinedFull.thm_crit_refined
#check @FourCorner.CriticalRefinedFull.exclusions_iff_infinite_pairs
#check @FourCorner.CriticalRefinedFull.exclusions_iff_literal_pattern
#print FourCorner.CriticalRefinedWave27.RefinedPattern
#print FourCorner.CriticalRefinedCompletion.PaperRefinedTriple
#print FourCorner.CriticalRefinedCompletion.PaperRefinedPairs
#print axioms FourCorner.RefinedFiniteSource.from_good_cover
#print axioms FourCorner.RefinedFiniteSource.refinedPattern_of_good_cover
#print axioms FourCorner.RefinedCoverHasse.hasse_bound
#print axioms FourCorner.RefinedBadCover.badCover_card
#print axioms FourCorner.RefinedBadCover.exists_good_cover_large
#print axioms FourCorner.RefinedBadCover.bad_base_le_eight_of_units
#print axioms FourCorner.RefinedBadCover.exists_good_cover_small_of_units
#print axioms FourCorner.RefinedFiniteExistence.pattern_large
#print axioms FourCorner.RefinedFiniteExistence.pattern_five_mod_eight
#print axioms FourCorner.RefinedFiniteExistence.allowed_refined_pattern
#print axioms FourCorner.CriticalRefinedFull.thm_crit_refined
#print axioms FourCorner.CriticalRefinedFull.exclusions_iff_infinite_pairs
#print axioms FourCorner.CriticalRefinedFull.exclusions_iff_literal_pattern
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    logInfo m!"AUDIT_IMPORT {m}"
