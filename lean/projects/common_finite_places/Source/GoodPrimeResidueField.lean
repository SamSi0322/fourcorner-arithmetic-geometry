import GoodPrimeParameters
import ResidueFullConstants
import ResidueCoefficientInstances

noncomputable section
namespace FourCorner.LocalPointCompatibility
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

/-- Outside exactly the stated exceptional set, reduction of the SAME t and
kappa gives a genuine finite-constant degree32 function field with full constants.
No special-fibre model or genus identification is asserted in this constituent. -/
theorem good_residue_field {t κ : ℚ} (ht : 1 < t)
    (hκ : κ ∈ Genus17Support.twists t) {p : ℕ} [Fact p.Prime]
    (hout : p ∉ exceptionalPrimes t) :
    ∃ T K : ℤ_[p], (T : ℚ_[p]) = t ∧ (K : ℚ_[p]) = κ ∧
      letI := ResidueCoefficientInstances.constantAlgebra (K := ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)
      let F := CommonGenus17Field.field (ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)
      Module.finrank (RatFunc (ZMod p)) F = 32 ∧
      AlgebraicCurve.IsCurveOver (ZMod p) F ∧ Algebra.EssFiniteType (ZMod p) F ∧
        AlgebraicCurve.ConstantsAreBase (ZMod p) F := by
  obtain ⟨T,K,hT,hK,ht0,ht1,htm,hk,hbranches⟩ := good_parameter_residues ht hκ hout
  refine ⟨T,K,hT,hK,?_⟩
  letI := ResidueCoefficientInstances.constantAlgebra (K := ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)
  letI : PerfectField (ZMod p) := PerfectField.ofFinite
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by have h := (outside_exceptionalPrimes hp hout).1; omega
  letI : NeZero (2 : ZMod p) := ⟨by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact hp.ne_one h
    · exact hp2 h⟩
  have ht1' : PadicInt.toZMod T ≠ 1 := by
    intro h
    exact ht1 (by simp only [map_sub,map_one,h,sub_self])
  have htm' : PadicInt.toZMod T ≠ -1 := by
    intro h
    exact htm (by simp only [map_add,map_one,h,neg_add_cancel])
  exact ⟨ResidueRadicalDegree.degree_thirty_two (ZMod p) ht0 ht1' htm' hk,
    ResidueRadicalField.isCurveOver (ZMod p) _ _,ResidueRadicalField.essFiniteType (ZMod p) _ _,
    ResidueFullConstants.constantsAreBase (ZMod p) ht0 ht1' htm' hk⟩

end FourCorner.LocalPointCompatibility
#print axioms FourCorner.LocalPointCompatibility.good_residue_field
