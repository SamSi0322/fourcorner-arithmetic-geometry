import HasseKnownCorrectedRows
import HassePositiveAOdd
import HasseOddPole

namespace FourCorner.HasseCorrectedOddProduct
open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HasseConstantCorrection HasseConstantOdd HasseParameterValuations HasseFiniteAssembly
open HasseObstructionArithmetic HasseSignAlgebra HasseWR HasseInertParity
open HasseKnownCorrectedRows HasseParameterSupport

/-- Full original-source positive-a correction, including odd ramified
and every even depth. Both actual signs are the same constant symbol. -/
theorem corrected_positive_a (q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : 0<padicValRat q.val (p-1)) :
    correctedSign p hp P D q.val=bitSign (expectedOddBit p q.val) := by
  have ht := HassePositiveAOdd.tangentSign_positive_a q p hp P D hv
  change tangentSign p hp P D q.val=constantSign p hp q.val at ht
  rw [correctedSign,ht,← pow_two,constantSign_sq_one]
  have hpv := positive_a_p_zero q p hp hv
  have hb := HasseInertParity.positive_a_b_zero q p hp hv
  simp [expectedOddBit,positiveTerm,poleTerm,hpv,hb,bitSign_zero]

/-- The literal minus sign at every odd-depth pole cancels against the
actual constant correction; the remaining character is precisely sigma. -/
theorem corrected_odd_pole (q : OddPrime) (p : ℚ) (hp : 1<p)
    (hL : HasseNorms.Loc p) (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : padicValRat q.val p<0) (hodd : Odd (padicValRat q.val p)) :
    correctedSign p hp P D q.val=bitSign (expectedOddBit p q.val) := by
  classical
  obtain ⟨ha,hb⟩ := pole_neighbors_equal q p hp hv
  have hbit : (padicValRat q.val p : ZMod 2)=1 := by
    have hh := hodd
    rw [Int.odd_iff] at hh
    rw [← ZMod.intCast_mod]
    norm_num only [Nat.cast_ofNat]
    rw [hh]
    norm_num
  have hc : constantSign p hp q.val=legendreSym q.val (-2) := by
    rw [constantSign_odd,ha,hbit]
    norm_num [ZMod.val_one_eq_one_mod]
  have he := rootTwo_sq q.val (pole_root_exists p hp hL q.val q.property.2 hodd)
  rw [correctedSign,HasseOddPole.tangentSign_odd_pole_character q p hp P D hv hodd (rootTwo q.val) he,
    hc,pole_character_correction q (rootTwo q.val) he]
  simp [expectedOddBit,positiveTerm,poleTerm,hb,not_lt_of_ge (le_of_lt hv),q.property.2,hv,hodd]

/-- Every actual odd completion, with the exhaustive parameter valuation
partition discharged and no missing-row premise. -/
theorem corrected_odd_pointwise (q : OddPrime) (p : ℚ) (hp : 1<p)
    (hL : HasseNorms.Loc p) (P : HomogeneousPoint p) (D : TangentData p P) :
    correctedSign p hp P D q.val=bitSign (expectedOddBit p q.val) := by
  rcases all_odd_branches q p hp with h | h | h | h | h | h
  · exact corrected_good q p hp P D h.1 h.2.1 h.2.2
  · exact corrected_positive_p q p hp P D h
  · exact corrected_positive_a q p hp P D h
  · exact corrected_positive_b q p hp hL P D h
  · exact corrected_even_pole q p hp P D h.1 h.2
  · exact corrected_odd_pole q p hp hL P D h.1 h.2

/-- Full original-source corrected odd product on precisely the paper's
finite parameter support, equal to the literal B+P bit. -/
theorem correctedOdd_product (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) :
    (∏ q ∈ oddParameterSupport p,correctedSign p hp P D q)=
      bitSign (B p+HasseObstructionArithmetic.P p) := by
  rw [← expectedOddSign_product p hp]
  apply Finset.prod_congr rfl
  intro q hq
  have hprime := oddParameterSupport_prime p q hq
  exact corrected_odd_pointwise ⟨q,hprime.1,hprime.2⟩ p hp hL P D

#print axioms corrected_positive_a
#print axioms corrected_odd_pole
#print axioms corrected_odd_pointwise
#print axioms correctedOdd_product
end FourCorner.HasseCorrectedOddProduct
