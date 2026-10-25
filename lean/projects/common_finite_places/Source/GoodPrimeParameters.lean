import ExceptionalPrimes
import CommonFinitePlacesHensel

noncomputable section
namespace FourCorner.LocalPointCompatibility

theorem rational_norm_one_of_valuation_zero {p : ℕ} [Fact p.Prime]
    {q : ℚ} (hq : q ≠ 0) (hv : padicValRat p q = 0) : ‖(q : ℚ_[p])‖ = 1 := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hq),Padic.valuation_ratCast,hv]
  simp

/-- Every exact allowed kappa is an actual p-adic integral unit outside the
paper's exceptional primes; no twisting-denominator exception is omitted. -/
theorem good_parameter_residues {t κ : ℚ} (ht : 1 < t)
    (hκ : κ ∈ Genus17Support.twists t) {p : ℕ} [Fact p.Prime]
    (hout : p ∉ exceptionalPrimes t) :
    ∃ T K : ℤ_[p], (T : ℚ_[p]) = t ∧ (K : ℚ_[p]) = κ ∧
      PadicInt.toZMod T ≠ 0 ∧ PadicInt.toZMod (T-1) ≠ 0 ∧
      PadicInt.toZMod (T+1) ≠ 0 ∧ PadicInt.toZMod K ≠ 0 ∧
      List.Pairwise (· ≠ ·)
        ([0,-(PadicInt.toZMod T+1),PadicInt.toZMod T-1,
          PadicInt.toZMod T+1,-(PadicInt.toZMod T-1)] : List (ZMod p)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨hpbig,htv,hsv,hTv⟩ := outside_exceptionalPrimes hp hout
  have hp2 : p ≠ 2 := by omega
  have ht0 : t ≠ 0 := by linarith
  have hs0 : t-1 ≠ 0 := by linarith
  have hT0 : t+1 ≠ 0 := by linarith
  have hnt := rational_norm_one_of_valuation_zero ht0 htv
  have hns := rational_norm_one_of_valuation_zero hs0 hsv
  have hnT := rational_norm_one_of_valuation_zero hT0 hTv
  let T := padicIntegral (t : ℚ_[p]) hnt.le
  have tunit : PadicInt.toZMod T ≠ 0 :=
    (padicInt_norm_eq_one_iff_residue_ne_zero T).mp hnt
  have sunit : PadicInt.toZMod (T-1) ≠ 0 := by
    apply (padicInt_norm_eq_one_iff_residue_ne_zero (T-1)).mp
    change ‖(t : ℚ_[p])-1‖ = 1
    simpa only [Rat.cast_sub,Rat.cast_one] using hns
  have Tunit : PadicInt.toZMod (T+1) ≠ 0 := by
    apply (padicInt_norm_eq_one_iff_residue_ne_zero (T+1)).mp
    change ‖(t : ℚ_[p])+1‖ = 1
    simpa only [Rat.cast_add,Rat.cast_one] using hnT
  have hd : padicValRat p (t^2-1) = 0 := by
    rw [show t^2-1 = (t-1)*(t+1) by ring,padicValRat.mul hs0 hT0,hsv,hTv,add_zero]
  obtain ⟨e,S,hS,hκeq⟩ := Genus17Support.mem_twists.mp hκ
  let K : ℤ_[p] := (if e then 2 else 1) * ∏ q ∈ S, (q : ℤ_[p])
  have hprod : PadicInt.toZMod (∏ q ∈ S, (q : ℤ_[p])) ≠ 0 := by
    apply CommonFinitePlaces.twisting_product_residue_ne_zero hp2 (t^2-1) S ?_ hd
    intro q hq
    have h := (Genus17Support.mem_oddSupport _ _).mp (hS hq)
    exact ⟨h.1,Or.inr h.2.2.1⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact hp.ne_one h
    · exact hp2 h
  have htwoMap : PadicInt.toZMod (2 : ℤ_[p]) = (2 : ZMod p) := by
    rw [show (2 : ℤ_[p]) = 1+1 by ring,map_add,map_one]
    ring
  have kunit : PadicInt.toZMod K ≠ 0 := by
    cases e
    · simpa [K] using hprod
    · change PadicInt.toZMod ((2 : ℤ_[p]) * ∏ q ∈ S, (q : ℤ_[p])) ≠ 0
      rw [map_mul,htwoMap]
      exact mul_ne_zero htwo hprod
  have htwoCoe : (PadicInt.Coe.ringHom (2 : ℤ_[p]) : ℚ_[p]) = (2 : ℚ_[p]) :=
    PadicInt.coe_natCast 2
  have kcoe : (K : ℚ_[p]) = (κ : ℚ_[p]) := by
    have h := congrArg (fun q : ℚ => (q : ℚ_[p])) hκeq.symm
    change (PadicInt.Coe.ringHom K : ℚ_[p]) = (κ : ℚ_[p])
    cases e <;> simpa [K,map_prod,htwoCoe] using h
  exact ⟨T,K,rfl,kcoe,tunit,sunit,Tunit,kunit,
    CommonFinitePlaces.residue_branch_sections_distinct hp2 T tunit sunit Tunit⟩

end FourCorner.LocalPointCompatibility
#print axioms FourCorner.LocalPointCompatibility.good_parameter_residues
