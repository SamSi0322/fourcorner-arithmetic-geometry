import CriticalDirectMap
import Mathlib.RingTheory.Algebraic.Integral

noncomputable section
namespace FourCorner.CriticalMapTranscendence
open CriticalConicParameter CriticalQuarticCubic CriticalDirectMap
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
set_option autoImplicit false
set_option maxHeartbeats 1500000

private theorem num (n : ℕ) : IsIntegral k (n : L) := by
  simpa only [map_natCast] using (isIntegral_algebraMap (x := (n : k)) : IsIntegral k (algebraMap k L (n:k)))
private theorem inv {z : L} (hz : IsIntegral k z) : IsIntegral k z⁻¹ :=
  (IsAlgebraic.inv_iff.mpr hz.isAlgebraic).isIntegral

theorem inverseA_algebraic {i x y : L} (hi : IsAlgebraic k i)
    (hx : IsAlgebraic k x) (hy : IsAlgebraic k y) :
    IsAlgebraic k (inverseA i x y) := by
  have hi' := hi.isIntegral
  have hx' := hx.isIntegral
  have hy' := hy.isIntegral
  have h1 : IsIntegral k (1:L) := by simpa only [Nat.cast_one] using (num (k := k) (L := L) 1)
  have h2 : IsIntegral k (2:L) := by simpa only [Nat.cast_ofNat] using (num (k := k) (L := L) 2)
  have h4 : IsIntegral k (4:L) := by simpa only [Nat.cast_ofNat] using (num (k := k) (L := L) 4)
  have hs : IsIntegral k (scale i) := h1.sub hi'
  have hX : IsIntegral k (inverseX i x) := hi'.add (hs.mul hx')
  have hL : IsIntegral k (inverseL i y) := (h4.mul hs).mul hy'
  have hv : IsIntegral k (inverseV (inverseX i x) (inverseL i y)) := by
    simpa only [inverseV,div_eq_mul_inv] using
      (hL.sub (h4.mul (h1.sub hX))).mul (inv (h2.mul ((hX.pow 2).sub h1)))
  have hu : IsIntegral k (inverseU i x y) := hv.add hi'
  have hD : IsIntegral k (denominator i (inverseU i x y)) := (hu.pow 2).sub hi'
  simpa only [inverseA,first,div_eq_mul_inv] using
    ((((hu.pow 2).sub (h2.mul hu)).add hi').mul (inv hD)).isAlgebraic

/-- The direct elliptic X coordinate is genuinely transcendental whenever
the original literal coordinate a is. This proves the injectivity needed
for the native E function-field map, without assuming that map is an iso. -/
theorem x_transcendental (i a b c : L) (hia : IsAlgebraic k i)
    (hi : i^2 = -1) (h2 : (2:L) ≠ 0)
    (hb : b^2-1=i*(a^2-1)) (hc : c^2-1=(1+i)*(a^2-1))
    (hshift : a^2-1 ≠ 0) (ha : Transcendental k a) :
    Transcendental k (CriticalDirectMap.x i a b c) := by
  intro hx
  have ha1 : a ≠ 1 := by intro h; apply hshift; rw [h]; ring
  have he := elliptic_equation i a b c hi h2 hb hc ha1
  have hy : IsAlgebraic k (CriticalDirectMap.y i a b c) := by
    have hsq : IsIntegral k (CriticalDirectMap.y i a b c ^2) := by
      rw [he]
      exact (hx.isIntegral.pow 3).sub hx.isIntegral
    exact (IsIntegral.of_pow (n := 2) (by decide) hsq).isAlgebraic
  have h := inverseA_algebraic hia hx hy
  rw [inverseA_forward i a b c hi h2 hb hc hshift] at h
  exact ha h

end FourCorner.CriticalMapTranscendence
#print axioms FourCorner.CriticalMapTranscendence.inverseA_algebraic
#print axioms FourCorner.CriticalMapTranscendence.x_transcendental
