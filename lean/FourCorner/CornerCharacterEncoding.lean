import FourCorner.CornerCharacterGProduct
import FourCorner.CornerCharacterSevenCount
import FourCorner.CornerReciprocityOpposite

set_option autoImplicit false
namespace FourCorner

/-- The paper's literal inert-prime valuation product on integers. The
positive arguments in Section 04 are actual integer half-sums, rather
than a separately normalized or sign-changed source. -/
def paperGInt (a : ℤ) : ℤ :=
  ∏ p ∈ a.natAbs.primeFactors.filter (fun p => p%4=3), (-1:ℤ)^padicValInt p a

@[simp] theorem paperGInt_natCast (a : ℕ) : paperGInt (a:ℤ)=paperG a := by
  simp only [paperGInt,paperG,padicValInt,Int.natAbs_natCast]

/-- Integer factorization uses the same full prime depths as the natural
valuation product. -/
theorem paperGInt_eq_oddPartChar_natAbs {a : ℤ} (ha : a ≠ 0) :
    paperGInt a=oddPartChar a.natAbs := by
  change paperG a.natAbs=oddPartChar a.natAbs
  exact paperG_eq_oddPartChar (Int.natAbs_pos.mpr ha)

namespace IntegralModel

/-- The literal valuation-product notation at the actual positive integer
half-sum agrees with the Jacobi odd-part encoding. -/
theorem actual_half_sum_character_encoding (M : IntegralModel) (i j : Bool × Bool) :
    paperGInt ((M.cornerRadius i+M.cornerRadius j)/2)=oddPartChar (M.pairHalfSumNat i j) := by
  rw [← M.pairHalfSumNat_cast,paperGInt_natCast]
  exact paperG_eq_oddPartChar (M.pairHalfSumNat_pos i j)

/-- The manuscript pair-reciprocity theorem with its primary literal G
notation: the product of (-1) raised to every inert-prime valuation. -/
theorem actual_pair_reciprocity_literal_G (M : IntegralModel) (hX : Odd M.X)
    {i j : Bool × Bool} (hne : i ≠ j) :
    paperGInt ((M.cornerRadius i+M.cornerRadius j)/2) ^
        (1+e4 (M.cornerClass i*M.cornerClass j)) =
      (-1:ℤ)^(e4 (M.cornerClass i)*e4 (M.cornerClass j)) *
        sigma16 (M.cornerClass i*M.cornerClass j)^((cornerDistanceSquared i j-1).toNat) := by
  rw [M.actual_half_sum_character_encoding]
  exact M.actual_pair_reciprocity hX hne

/-- The primary modulo-four exponent of each canonical colour is exactly
the parity of its seven-modulo-eight prime-factor count. -/
theorem corner_sevenPrimeCount_parity (M : IntegralModel) (c : Bool × Bool) :
    sevenPrimeCount (M.cornerClass c)%2=e4 (M.cornerClass c) := by
  apply sevenPrimeCount_parity (M.cornerClass_pos c) (M.cornerClass_squarefree c)
  intro p hp hd
  obtain ⟨hL,hxy⟩ := M.basic_mod_four
  exact M.cornerClass_prime_support (Int.dvd_of_emod_eq_zero hL) (by omega) c hp hd

/-- Pairwise coprimality retains each prime exactly once in a product of
two distinct canonical colours. -/
theorem pair_sevenPrimeCount_parity (M : IntegralModel) {c d : Bool × Bool}
    (hne : c ≠ d) :
    sevenPrimeCount (M.cornerClass c*M.cornerClass d)%2=
      e4 (M.cornerClass c*M.cornerClass d) := by
  apply sevenPrimeCount_parity (Nat.mul_pos (M.cornerClass_pos c) (M.cornerClass_pos d))
    ((Nat.squarefree_mul (M.cornerClass_pairwise_coprime hne)).mpr
      ⟨M.cornerClass_squarefree c,M.cornerClass_squarefree d⟩)
  intro p hp hd
  obtain ⟨hL,hxy⟩ := M.basic_mod_four
  rcases hp.dvd_mul.mp hd with hc | hd
  · exact M.cornerClass_prime_support (Int.dvd_of_emod_eq_zero hL) (by omega) c hp hc
  · exact M.cornerClass_prime_support (Int.dvd_of_emod_eq_zero hL) (by omega) d hp hd

/-- Literal prime-factor-count form of the parity refinement in the
opposite-colour theorem. -/
theorem opposite_colour_literal_seven_parity (M : IntegralModel) (hX : Odd M.X)
    {c d : Bool × Bool} (he : c.1 ≠ d.1) (hf : c.2 ≠ d.2) :
    (M.cornerClass c*M.cornerClass d)%16=
      if sevenPrimeCount (M.cornerClass c*M.cornerClass d)%2=0 then 1 else 15 := by
  have hne : c ≠ d := fun h => he (congrArg Prod.fst h)
  rw [M.pair_sevenPrimeCount_parity hne]
  exact M.opposite_colour_residue_refinement hX he hf

/-- Pair reciprocity with both the literal inert-prime product and literal
seven-prime count parities. -/
theorem actual_pair_reciprocity_literal_characters (M : IntegralModel) (hX : Odd M.X)
    {i j : Bool × Bool} (hne : i ≠ j) :
    paperGInt ((M.cornerRadius i+M.cornerRadius j)/2) ^
        (1+sevenPrimeCount (M.cornerClass i*M.cornerClass j)%2) =
      (-1:ℤ)^((sevenPrimeCount (M.cornerClass i)%2)*(sevenPrimeCount (M.cornerClass j)%2)) *
        sigma16 (M.cornerClass i*M.cornerClass j)^((cornerDistanceSquared i j-1).toNat) := by
  rw [M.corner_sevenPrimeCount_parity i,M.corner_sevenPrimeCount_parity j,
    M.pair_sevenPrimeCount_parity hne]
  exact M.actual_pair_reciprocity_literal_G hX hne

/-- The complete two-row residue table for the kernel and its two opposite
products, in their original corner labels. -/
theorem opposite_colour_residue_table (M : IntegralModel) (hX : Odd M.X) :
    let b := M.cornerClass (false,false)*M.cornerClass (true,true)
    let c := M.cornerClass (true,false)*M.cornerClass (false,true)
    (M.cornerKernel%16=1 ∧ ((b%16=1 ∧ c%16=1) ∨ (b%16=15 ∧ c%16=15))) ∨
    (M.cornerKernel%16=15 ∧ ((b%16=1 ∧ c%16=15) ∨ (b%16=15 ∧ c%16=1))) := by
  dsimp only
  have hk : M.cornerKernel=(M.cornerClass (false,false)*M.cornerClass (true,true))*
      (M.cornerClass (true,false)*M.cornerClass (false,true)) := by
    dsimp [cornerKernel]
    ring
  rw [hk]
  obtain ⟨hb,hc⟩ := M.opposite_colour_congruences hX
  rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    norm_num [Nat.mul_mod,hb,hc]

end IntegralModel
end FourCorner
#print axioms FourCorner.paperGInt_eq_oddPartChar_natAbs
#print axioms FourCorner.IntegralModel.actual_half_sum_character_encoding
#print axioms FourCorner.IntegralModel.actual_pair_reciprocity_literal_G

#print axioms FourCorner.IntegralModel.corner_sevenPrimeCount_parity
#print axioms FourCorner.IntegralModel.opposite_colour_literal_seven_parity
#print axioms FourCorner.IntegralModel.actual_pair_reciprocity_literal_characters
#print axioms FourCorner.IntegralModel.opposite_colour_residue_table
