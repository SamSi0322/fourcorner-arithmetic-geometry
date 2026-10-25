import GoodPrimeRationalPlace
import FinitePlaceRealization
import InfinityPlaceRealization

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.LocalPointCompatibility
open RadicalLinearization
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Hasse--Weil selects an ACTUAL rational place. Its finite/branch/infinity
residues yield one simultaneous transcendental p-adic five-root solution
with the SAME original rational parameters. No good model or local point
is included as a hypothesis. -/
theorem good_prime_source {t κ : ℚ} (ht : 1<t)
    (hκ : κ ∈ Genus17Support.twists t) {p : ℕ} [Fact p.Prime]
    (hout : p ∉ exceptionalPrimes t) :
    ∃ (e : ℚ_[p]) (r : Fin 5 → ℚ_[p]), Transcendental ℚ e ∧
      ∀ i, r i^2 = values (t : ℚ_[p]) ((κ : ℚ_[p])⁻¹) e i := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by have := (outside_exceptionalPrimes hp hout).1; omega
  have hκ0 : κ ≠ 0 := Genus17Support.twist_ne_zero hκ
  obtain ⟨T,K,hT,hK,ht0,ht1,htm,hk,hplace⟩ := good_prime_rational_place ht hκ hout
  letI := ResidueCoefficientInstances.constantAlgebra (K := ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K)
  obtain ⟨w,hw⟩ := hplace
  by_cases hl : ell (ZMod p) (PadicInt.toZMod T) (PadicInt.toZMod K) ∈ w.toValuationSubring
  · exact FinitePlaceRealization.realize hp2 t κ ht hκ0 T K hT hK ht0 ht1 htm hk w hw hl
  · exact InfinityPlaceRealization.realize hp2 t κ hκ0 T K hT hK ht0 ht1 htm hk w hw hl

/-- Every exact allowed twist has an actual Qp-valued point on the SAME
canonical genus17 cover outside precisely the stated exceptional primes. -/
theorem good_prime_point {t κ : ℚ} (ht : 1<t)
    (hκ : κ ∈ Genus17Support.twists t) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    {p : ℕ} [Fact p.Prime] (hout : p ∉ exceptionalPrimes t) :
    Nonempty (Spec (CommRingCat.of ℚ_[p]) ⟶ Genus17Geometry.curve t κ h0 h1 hm) := by
  exact FiniteHenselRealization.actual_point ht (Genus17Support.twist_ne_zero hκ)
    (good_prime_source ht hκ hout)

end FourCorner.LocalPointCompatibility
#print axioms FourCorner.LocalPointCompatibility.good_prime_source
#print axioms FourCorner.LocalPointCompatibility.good_prime_point
