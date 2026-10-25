import ResidueDegreeOnePlace
import GoodPrimeResidueField

noncomputable section
open AlgebraicCurve
namespace FourCorner.LocalPointCompatibility
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

/-- Outside the exact exceptional set, the SAME t,kappa reductions have an
ACTUAL rational place of their literal degree32 genus17 residue function field.
This is not yet a Qp-point assertion or an assumed special-fibre model. -/
theorem good_prime_rational_place {t κ : ℚ} (ht : 1 < t)
    (hκ : κ ∈ Genus17Support.twists t) {p : ℕ} [Fact p.Prime]
    (hout : p ∉ exceptionalPrimes t) :
    ∃ T K : ℤ_[p], (T : ℚ_[p]) = t ∧ (K : ℚ_[p]) = κ ∧
      PadicInt.toZMod T ≠ 0 ∧ PadicInt.toZMod (T-1) ≠ 0 ∧
      PadicInt.toZMod (T+1) ≠ 0 ∧ PadicInt.toZMod K ≠ 0 ∧
      letI := ResidueCoefficientInstances.constantAlgebra (K := ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)
      ∃ w : Place (ZMod p) (CommonGenus17Field.field (ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)),
        w.IsRational := by
  obtain ⟨T,K,hT,hK,ht0,ht1,htm,hk,hbranches⟩ := good_parameter_residues ht hκ hout
  refine ⟨T,K,hT,hK,ht0,ht1,htm,hk,?_⟩
  letI := ResidueCoefficientInstances.constantAlgebra (K := ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)
  have hp : p.Prime := Fact.out
  have hpbig := (outside_exceptionalPrimes hp hout).1
  have hp2 : p ≠ 2 := by omega
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
  have hcard : 1153 < Nat.card (ZMod p) := by
    simpa only [Nat.card_eq_fintype_card,ZMod.card] using hpbig
  exact ResidueDegreeOnePlace.exists_rational (ZMod p) ht0 ht1' htm' hk hcard

end FourCorner.LocalPointCompatibility
#print axioms FourCorner.LocalPointCompatibility.good_prime_rational_place
