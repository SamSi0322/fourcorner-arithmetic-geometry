/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in ../LICENSE.
The valuation argument below adapts Michael Stoll's proved
`points_eq_zero_of_nsmul_prime_ne` from the pinned ReductionAtPrime cone.
It replaces its prime-order hypotheses by the precise scalar-unit hypothesis.
-/
import EllipticCurves.WeierstrassFormalGroup.Filtration

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsLocalRing WithZero ChabautyColeman

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R}
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}

/-- A unit scalar cannot annihilate a nonzero point of the actual integral
Weierstrass formal group. No good reduction or ramification bound is assumed. -/
theorem formal_points_eq_zero_of_unit_nsmul {n : ℕ}
    (hn : IsUnit (n : v.adicCompletionIntegers K))
    {z : W₀.formalGroupLaw.Points} (hz : n • z = 0) : z = 0 := by
  by_contra hz0
  have ht0 : (z () : v.adicCompletionIntegers K) ≠ 0 :=
    fun h ↦ hz0 (funext fun i ↦ by cases i; exact Subtype.ext h)
  obtain ⟨k, hk1, hkv⟩ := ChabautyColeman.exists_valued_eq_exp_neg (z ()).2 ht0
  have htk : (z () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ k :=
    (v.mem_maximalIdeal_pow_iff (K := K)).mpr hkv.le
  have hcong := (W₀.nsmul_apply_coe_mem_and_sub_mem
    (Nat.one_le_iff_ne_zero.mp hk1) htk n).2
  rw [hz, FormalGroupLaw.zero_apply_coe, zero_sub, nsmul_eq_mul] at hcong
  obtain ⟨u, hu⟩ := hn.exists_left_inv
  have ht2k : (z () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (2 * k) := by
    rw [show (z () : v.adicCompletionIntegers K) =
      u * ((n : v.adicCompletionIntegers K) * (z () : v.adicCompletionIntegers K)) by
        rw [← mul_assoc, hu, one_mul]]
    exact Ideal.mul_mem_left _ _ (by simpa using neg_mem hcong)
  have hle := (v.mem_maximalIdeal_pow_iff (K := K)).mp ht2k
  rw [hkv, exp_le_exp] at hle
  push_cast at hle
  lia

variable {W : Affine (v.adicCompletion K)} [W.IsElliptic]
  [DecidableEq (v.adicCompletion K)] [CharZero K]
  {hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W}

/-- The actual first filtration group has no torsion killed by a unit scalar.
The integral model and special fibre need not have good reduction. -/
theorem eq_zero_of_unit_nsmul_of_mem_filtration {n : ℕ}
    (hn : IsUnit (n : v.adicCompletionIntegers K))
    {P : W.Point} (hP : P ∈ filtration hW 0) (hkill : n • P = 0) : P = 0 := by
  obtain ⟨θ, _⟩ := exists_points_equiv_filtration (hW := hW)
  have hz : n • θ.symm ⟨P, hP⟩ = 0 := by
    rw [← map_nsmul, show n • (⟨P, hP⟩ : filtration hW 0) = 0 from
      Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact hkill), map_zero]
  have hzz := formal_points_eq_zero_of_unit_nsmul hn hz
  have h1 := congrArg θ hzz
  rw [θ.apply_symm_apply, map_zero] at h1
  simpa using congrArg Subtype.val h1

/-- Prime-to-residue-characteristic torsion vanishes in the actual first
filtration group, with no restriction on ramification. -/
theorem eq_zero_of_nsmul_of_mem_filtration_of_not_dvd {p n : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hn : ¬ p ∣ n) {P : W.Point} (hP : P ∈ filtration hW 0)
    (hkill : n • P = 0) : P = 0 :=
  eq_zero_of_unit_nsmul_of_mem_filtration (isUnit_natCast_of_not_dvd hp hpmem hn) hP hkill

/-- At residue characteristic two, the actual first filtration group has no
nonzero odd torsion, including for an integral model with bad reduction. -/
theorem eq_zero_of_odd_nsmul_of_mem_filtration {n : ℕ}
    (h2 : (2 : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hn : Odd n) {P : W.Point} (hP : P ∈ filtration hW 0)
    (hkill : n • P = 0) : P = 0 :=
  eq_zero_of_nsmul_of_mem_filtration_of_not_dvd Nat.prime_two h2 hn.not_two_dvd_nat hP hkill

/-- The preceding odd-torsion theorem with the prime-above-two condition
stated in the original Dedekind domain instead of its completion. -/
theorem eq_zero_of_odd_nsmul_of_mem_filtration_of_two_mem {n : ℕ}
    (h2 : (2 : R) ∈ v.asIdeal) (hn : Odd n)
    {P : W.Point} (hP : P ∈ filtration hW 0) (hkill : n • P = 0) : P = 0 := by
  have h2m : (2 : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) := by
    have hh := (v.algebraMap_mem_maximalIdeal_pow_iff (K := K) (r := (2 : R)) (n := 1)).mpr
      (by simpa using h2)
    simpa only [pow_one, map_ofNat] using hh
  exact eq_zero_of_odd_nsmul_of_mem_filtration h2m hn hP hkill

/-- A concrete quotient-exponent-four bridge: if four times an odd-torsion
point lies in the actual first filtration group above two, the point is zero.
The inclusion premise remains an explicit obligation about the actual curve. -/
theorem eq_zero_of_odd_nsmul_of_four_nsmul_mem_filtration {n : ℕ}
    (h2 : (2 : R) ∈ v.asIdeal) (hn : Odd n) {P : W.Point}
    (hfour : 4 • P ∈ filtration hW 0) (hkill : n • P = 0) : P = 0 := by
  have hkill4 : n • (4 • P) = 0 := by
    rw [smul_comm n 4 P, hkill, smul_zero]
  have h4 : 4 • P = 0 :=
    eq_zero_of_odd_nsmul_of_mem_filtration_of_two_mem h2 hn hfour hkill4
  have hd4 : addOrderOf P ∣ 4 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h4
  have hdn : addOrderOf P ∣ n := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkill
  have hc : Nat.Coprime 4 n := by
    simpa using (Nat.prime_two.coprime_iff_not_dvd.mpr hn.not_two_dvd_nat).pow_left 2
  have hd1 : addOrderOf P ∣ 1 := by
    simpa [hc.gcd_eq_one] using Nat.dvd_gcd hd4 hdn
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)

end WeierstrassCurve.Affine
