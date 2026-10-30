import RefinedBadCover
import CriticalNonsquareIUnits
import CriticalBoundaryCharacter

noncomputable section
namespace FourCorner.RefinedFiniteExistence
open AlgebraicCurve CriticalRadicalField CriticalRefinedWave27 RefinedFiniteSource RefinedBadCover
variable {p:ℕ} [Fact p.Prime]
set_option maxHeartbeats 2000000

/-- Actual cover Hasse and the genuine bad-place union give the original
signed refined pattern for every permitted prime at least73. -/
theorem pattern_large (hmod:p%4=1) (hlarge:73≤p) : RefinedPattern p := by
  have hp2:p≠2 := by omega
  have h2:(2:ZMod p)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp2)
  obtain ⟨i,hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p:=p)).mpr (by omega)
  have hi2:i^2= -1 := by simpa only [pow_two] using hi.symm
  obtain ⟨w,hw,hg⟩ := exists_good_cover_large i hi2 h2
    (by simpa only [Nat.card_eq_fintype_card,ZMod.card] using hlarge)
  exact refinedPattern_of_good_cover i hi2 h2 w hw hg

/-- In the5mod8 class, actual nonsquareness of i excludes EVERY original
zero coordinate and pole. Hence the actual base-eight boundary alone can
be bad, and at most16 actual cover places are excluded. -/
theorem pattern_five_mod_eight (hmod:p%4=1) (hfive:p%8=5) (hlarge:29≤p) : RefinedPattern p := by
  have hp2:p≠2 := by omega
  have h2:(2:ZMod p)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp2)
  obtain ⟨i,hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p:=p)).mpr (by omega)
  have hi2:i^2= -1 := by simpa only [pow_two] using hi.symm
  have hns:¬IsSquare i := by
    rw [CriticalBoundaryCharacter.square_i_iff_mod_eight hmod i hi2]
    omega
  obtain ⟨w,hw,hg⟩ := exists_good_cover_small_of_units i hi2 h2
    (by simpa only [Nat.card_eq_fintype_card,ZMod.card] using hlarge)
    (CriticalNonsquareIUnits.all_units i hi2 h2 hns)
  exact refinedPattern_of_good_cover i hi2 h2 w hw hg

/-- Full finite-field direction(i)->(ii), on the ORIGINAL RefinedPattern.
Small41 uses the original exact witness;5,13,17 are not silently dropped. -/
theorem allowed_refined_pattern (hmod:p%4=1) (h5:p≠5) (h13:p≠13) (h17:p≠17) : RefinedPattern p := by
  by_cases hone:p%8=1
  · by_cases hsmall:p<73
    · rcases CriticalRefinedNumerics.small_one_mod_eight p Fact.out hone hsmall with hp17|hp41
      · exact False.elim (h17 hp17)
      · subst p;exact refined41
    · exact pattern_large hmod (by omega)
  · have hfive:p%8=5 := by omega
    by_cases hsmall:p<29
    · rcases CriticalRefinedNumerics.small_five_mod_eight p Fact.out hfive hsmall with hp5|hp13
      · exact False.elim (h5 hp5)
      · exact False.elim (h13 hp13)
    · exact pattern_five_mod_eight hmod hfive (by omega)

#print axioms pattern_large
#print axioms pattern_five_mod_eight
#print axioms allowed_refined_pattern
end FourCorner.RefinedFiniteExistence
