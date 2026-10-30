import HasseParameterValuations
import HasseOddSourceRows
import HassePositiveBInert
import HassePositiveAEven
import HasseEvenPole
import HasseConstantOdd

namespace FourCorner.HasseKnownCorrectedRows

open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HasseConstantCorrection HasseConstantOdd HasseParameterValuations HasseFiniteAssembly
open HasseObstructionArithmetic HasseSignAlgebra HasseWR HasseInertParity

theorem corrected_good (q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : padicValRat q.val p=0) (ha : padicValRat q.val (p-1)=0) (hb : padicValRat q.val (p+1)=0) :
    correctedSign p hp P D q.val=bitSign (expectedOddBit p q.val) := by
  have hc : constantSign p hp q.val=1 := constantSign_odd_even q p hp (by rw [ha];exact ⟨0,by simp⟩)
  rw [correctedSign,HasseGoodUnitRow.tangentSign_good_unit q p hp P D hv ha hb,hc,one_mul]
  simp only [expectedOddBit,positiveTerm,poleTerm,hv,hb,lt_self_iff_false,and_false,false_and,
    ite_false,zero_add,bitSign_zero]

theorem corrected_positive_p (q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hv : 0<padicValRat q.val p) :
    correctedSign p hp P D q.val=bitSign (expectedOddBit p q.val) := by
  obtain ⟨ha,hb⟩ := positive_p_neighbors_zero q p hp hv
  have hc : constantSign p hp q.val=1 := constantSign_odd_even q p hp (by rw [ha];exact ⟨0,by simp⟩)
  rw [correctedSign,HasseOddSourceRows.tangentSign_positive_p q p hp P D hv,hc,one_mul]
  simp only [expectedOddBit,positiveTerm,poleTerm,hb,lt_self_iff_false,and_false,false_and,
    not_lt_of_ge (le_of_lt hv),ite_false,zero_add,bitSign_zero]

theorem corrected_positive_b (q : OddPrime) (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hv : 0<padicValRat q.val (p+1)) :
    correctedSign p hp P D q.val=bitSign (expectedOddBit p q.val) := by
  classical
  obtain ⟨hpv,ha⟩ := positive_b_neighbors_zero q p hp hv
  have hc : constantSign p hp q.val=1 := constantSign_odd_even q p hp (by rw [ha];exact ⟨0,by simp⟩)
  rw [correctedSign,hc,mul_one]
  by_cases h2 : IsSquare (2 : ZMod q.val)
  · have h2q : IsSquare (2 : ℚ_[q.val]) := by
      have h2n : (2 : ZMod q.val) ≠ 0 := by
        intro hz
        have hd := (ZMod.natCast_eq_zero_iff 2 q.val).mp hz
        exact q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left q.property.1.ne_one)
      have hmap : PadicInt.toZMod (2 : ℤ_[q.val])=(2 : ZMod q.val) := map_ofNat _ 2
      have hu : PadicInt.toZMod (2 : ℤ_[q.val]) ≠ 0 := by rwa [hmap]
      have hs := (padicInt_isSquare_coe_iff_residue_unit q.property.2 (2 : ℤ_[q.val]) hu).mpr
        (by rwa [hmap])
      have hcoe := PadicInt.coe_natCast (p:=q.val) 2
      norm_num only [Nat.cast_ofNat] at hcoe
      rwa [hcoe] at hs
    rw [HasseOddSourceRows.tangentSign_positive_b_split q p hp P D hv h2q]
    simp [expectedOddBit,positiveTerm,poleTerm,h2,hpv,bitSign_zero]
  · rw [HassePositiveBInert.tangentSign_positive_b_inert_half q p hp hL P D h2 hv]
    simp [expectedOddBit,positiveTerm,poleTerm,hpv,q.property.2,h2,hv,bitSign]

theorem corrected_positive_a_even (q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : 0<padicValRat q.val (p-1)) (he : Even (padicValRat q.val (p-1))) :
    correctedSign p hp P D q.val=bitSign (expectedOddBit p q.val) := by
  have ht := HassePositiveAEven.tangentSign_positive_a_even_constant q p hp P D hv he
  change tangentSign p hp P D q.val=constantSign p hp q.val at ht
  rw [correctedSign,ht,← pow_two,constantSign_sq_one]
  have hpv := positive_a_p_zero q p hp hv
  have hb := HasseInertParity.positive_a_b_zero q p hp hv
  simp [expectedOddBit,positiveTerm,poleTerm,hpv,hb,bitSign_zero]

theorem corrected_even_pole (q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : padicValRat q.val p<0) (he : Even (padicValRat q.val p)) :
    correctedSign p hp P D q.val=bitSign (expectedOddBit p q.val) := by
  obtain ⟨ha,hb⟩ := pole_neighbors_equal q p hp hv
  have hc : constantSign p hp q.val=1 := constantSign_odd_even q p hp (ha.symm ▸ he)
  rw [correctedSign,HasseEvenPole.tangentSign_even_pole q p hp P D hv he,hc,one_mul]
  have hnodd : ¬Odd (padicValRat q.val p) := fun ho => (Int.not_even_iff_odd.mpr ho) he
  simp [expectedOddBit,positiveTerm,poleTerm,hb,not_lt_of_ge (le_of_lt hv),hnodd,bitSign_zero]

#print axioms corrected_good
#print axioms corrected_positive_p
#print axioms corrected_positive_b
#print axioms corrected_positive_a_even
#print axioms corrected_even_pole

end FourCorner.HasseKnownCorrectedRows
