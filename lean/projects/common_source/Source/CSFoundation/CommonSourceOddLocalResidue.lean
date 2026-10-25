import FourCorner.CommonRootPadicResidue
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

set_option autoImplicit false

namespace FourCorner

/-- A nonsquare reduction of the cross product obstructs a quotient square
in the completed field. This does not impose a bound on any square root. -/
theorem commonSource_ratio_nonsquare_of_residue {p : ℕ} [Fact p.Prime]
    (u v : ℤ_[p]) (hres : ¬ IsSquare (PadicInt.toZMod (u * v))) :
    ¬ IsSquare ((u : ℚ_[p]) / (v : ℚ_[p])) := by
  have hv : v ≠ 0 := by
    intro h
    apply hres
    simp [h]
  have hv' : (v : ℚ_[p]) ≠ 0 := by
    intro h
    exact hv (PadicInt.ext h)
  intro hs
  apply padicInt_not_isSquare_coe_of_residue (u * v) hres
  have hs' := hs.mul (IsSquare.sq (v : ℚ_[p]))
  have heq : (u : ℚ_[p]) / (v : ℚ_[p]) * (v : ℚ_[p]) ^ 2 =
      ((u * v : ℤ_[p]) : ℚ_[p]) := by
    push_cast
    field_simp
  exact heq ▸ hs'

/-- The two exceptional residue constants at primes congruent to five mod
 eight. Both signs of two are nonsquares. -/
theorem commonSource_two_negTwo_nonsquare {p : ℕ} [Fact p.Prime]
    (hp8 : p % 8 = 5) :
    ¬ IsSquare (2 : ZMod p) ∧ ¬ IsSquare (-2 : ZMod p) := by
  have hp : p ≠ 2 := by omega
  constructor
  · rw [ZMod.exists_sq_eq_two_iff hp]
    omega
  · rw [ZMod.exists_sq_eq_neg_two_iff hp]
    omega

/-- The residue disk of the positive two-torsion point gives a nonsquare
common-source quotient at every depth in the disk. -/
theorem commonSource_both_plus_nonsquare {p : ℕ} [Fact p.Prime]
    (a c n : ℤ_[p])
    (ha : PadicInt.toZMod a = PadicInt.toZMod n)
    (hc : PadicInt.toZMod c = PadicInt.toZMod n)
    (hn : PadicInt.toZMod n ≠ 0) (h2 : ¬ IsSquare (2 : ZMod p)) :
    ¬ IsSquare (((a : ℚ_[p]) + (c : ℚ_[p])) / (2 * ((c : ℚ_[p]) + (n : ℚ_[p])))) := by
  apply commonSource_ratio_nonsquare_of_residue (a + c) (2 * (c + n))
  intro hs
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    exact h2 (h ▸ IsSquare.zero)
  simp only [map_mul, map_add, map_ofNat, ha, hc] at hs
  have hs' := hs.div (IsSquare.sq (2 * PadicInt.toZMod n))
  have heq : (PadicInt.toZMod n + PadicInt.toZMod n) *
      (2 * (PadicInt.toZMod n + PadicInt.toZMod n)) /
      (2 * PadicInt.toZMod n) ^ 2 = 2 := by
    field_simp
    ring
  exact h2 (heq ▸ hs')

/-- The exact square rescaling used in the negative two-torsion disk.
Its proof is an identity in the completed field, independent of depth. -/
theorem commonSource_negative_disk_rescale {p : ℕ} [Fact p.Prime]
    (a c n e : ℚ_[p]) (he : e ≠ 0)
    (hcurve : e ^ 2 = c * (c - n) * (c + n)) :
    (2 * e) ^ 2 * ((a + c) / (2 * (c + n))) =
      2 * (a + c) * c * (c - n) := by
  have hcn : c + n ≠ 0 := by
    intro hz
    have : e ^ 2 = 0 := by rw [hcurve, hz, mul_zero]
    exact he (sq_eq_zero_iff.mp this)
  rw [mul_pow, hcurve]
  field_simp

/-- An explicit nonsquare residue for the rescaled expression gives the
all-depth negative-disk obstruction. -/
theorem commonSource_both_minus_nonsquare_of_residue {p : ℕ} [Fact p.Prime]
    (a c n : ℤ_[p]) (e : ℚ_[p]) (he : e ≠ 0)
    (hcurve : e ^ 2 = (c : ℚ_[p]) * ((c : ℚ_[p]) - (n : ℚ_[p])) * ((c : ℚ_[p]) + (n : ℚ_[p])))
    (ha : PadicInt.toZMod a = -PadicInt.toZMod n)
    (hc : PadicInt.toZMod c = -PadicInt.toZMod n)
    (hres : ¬ IsSquare (-8 * PadicInt.toZMod n ^ 3)) :
    ¬ IsSquare (((a : ℚ_[p]) + (c : ℚ_[p])) / (2 * ((c : ℚ_[p]) + (n : ℚ_[p])))) := by
  intro hs
  have hs' := (IsSquare.sq (2 * e)).mul hs
  rw [commonSource_negative_disk_rescale (a : ℚ_[p]) c n e he hcurve] at hs'
  have hred := padicInt_isSquare_toZMod_of_isSquare_coe
    (2 * (a + c) * c * (c - n)) hs'
  apply hres
  convert hred using 1
  simp only [map_mul, map_add, map_sub, map_ofNat, ha, hc]
  ring

/-- The rescaled residue in the negative disk is nonsquare whenever the
parameter is a nonzero square and negative two is a nonsquare. -/
theorem commonSource_neg_eight_cube_nonsquare {K : Type*} [Field K] {n : K}
    (h2 : ¬ IsSquare (-2 : K)) (hn : IsSquare n) (hn0 : n ≠ 0) :
    ¬ IsSquare (-8 * n ^ 3) := by
  have h20 : (2 : K) ≠ 0 := by
    intro h
    apply h2
    simp [h]
  intro hs
  have hsq : IsSquare ((2 * n) ^ 2 * n) := (IsSquare.sq _).mul hn
  have hquot := hs.div hsq
  have heq : -8 * n ^ 3 / ((2 * n) ^ 2 * n) = (-2 : K) := by
    field_simp
    ring
  exact h2 (heq ▸ hquot)

/-- Arithmetic specialization of the positive-disk obstruction. -/
theorem commonSource_both_plus_nonsquare_mod_eight {p : ℕ} [Fact p.Prime]
    (hp8 : p % 8 = 5) (a c n : ℤ_[p])
    (ha : PadicInt.toZMod a = PadicInt.toZMod n)
    (hc : PadicInt.toZMod c = PadicInt.toZMod n)
    (hn : PadicInt.toZMod n ≠ 0) :
    ¬ IsSquare (((a : ℚ_[p]) + (c : ℚ_[p])) / (2 * ((c : ℚ_[p]) + (n : ℚ_[p])))) :=
  commonSource_both_plus_nonsquare a c n ha hc hn
    (commonSource_two_negTwo_nonsquare hp8).1

/-- Arithmetic specialization of the negative-disk obstruction, valid at
arbitrary depth and with the actual completed-field curve equation. -/
theorem commonSource_both_minus_nonsquare_mod_eight {p : ℕ} [Fact p.Prime]
    (hp8 : p % 8 = 5) (a c n : ℤ_[p]) (e : ℚ_[p]) (he : e ≠ 0)
    (hcurve : e ^ 2 = (c : ℚ_[p]) * ((c : ℚ_[p]) - (n : ℚ_[p])) * ((c : ℚ_[p]) + (n : ℚ_[p])))
    (ha : PadicInt.toZMod a = -PadicInt.toZMod n)
    (hc : PadicInt.toZMod c = -PadicInt.toZMod n)
    (hn : PadicInt.toZMod n ≠ 0) (hnsq : IsSquare (PadicInt.toZMod n)) :
    ¬ IsSquare (((a : ℚ_[p]) + (c : ℚ_[p])) / (2 * ((c : ℚ_[p]) + (n : ℚ_[p])))) :=
  commonSource_both_minus_nonsquare_of_residue a c n e he hcurve ha hc
    (commonSource_neg_eight_cube_nonsquare
      (commonSource_two_negTwo_nonsquare hp8).2 hnsq hn)

/-- A unit denominator makes the quotient integral and reduction commutes
with the quotient. The integral representative is the actual field value. -/
theorem commonSource_ratio_integral_residue {p : ℕ} [Fact p.Prime]
    (u v : ℤ_[p]) (hv : PadicInt.toZMod v ≠ 0) :
    ∃ h : ‖(u : ℚ_[p]) / (v : ℚ_[p])‖ ≤ 1,
      padicResidue ((u : ℚ_[p]) / (v : ℚ_[p])) h =
        PadicInt.toZMod u / PadicInt.toZMod v := by
  have hvnorm := padicInt_norm_coe_eq_one_of_residue_ne_zero v hv
  have hv0 : (v : ℚ_[p]) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hvnorm
    norm_num at hvnorm
  have h : ‖(u : ℚ_[p]) / (v : ℚ_[p])‖ ≤ 1 := by
    rw [norm_div, hvnorm, div_one]
    exact u.2
  refine ⟨h, ?_⟩
  let z : ℤ_[p] := padicIntegral ((u : ℚ_[p]) / (v : ℚ_[p])) h
  have hz : z * v = u := by
    apply PadicInt.ext
    exact div_mul_cancel₀ (u : ℚ_[p]) hv0
  have hred := congrArg (PadicInt.toZMod : ℤ_[p] →+* ZMod p) hz
  apply (eq_div_iff hv).mpr
  simpa only [map_mul, z, padicResidue] using hred

/-- At these primes a fourth root of unity is a nonsquare; this records
the odd cyclic coordinate obstruction without assuming it. -/
theorem commonSource_sqrt_neg_one_nonsquare_mod_eight {p : ℕ} [Fact p.Prime]
    (hp8 : p % 8 = 5) {i : ZMod p} (hi : i ^ 2 = -1) :
    ¬ IsSquare i := by
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    exact (commonSource_two_negTwo_nonsquare hp8).1 (h ▸ IsSquare.zero)
  rintro ⟨r, hr⟩
  have hr4 : r ^ 4 = -1 := by
    calc
      r ^ 4 = (r * r) ^ 2 := by ring
      _ = i ^ 2 := by rw [← hr]
      _ = -1 := hi
  have hr0 : r ≠ 0 := by
    intro h
    simp [h] at hr4
  have hexp : p - 1 = 4 * (2 * (p / 8) + 1) := by omega
  have hfermat := ZMod.pow_card_sub_one_eq_one hr0
  rw [hexp, pow_mul, hr4, pow_add, pow_mul] at hfermat
  norm_num at hfermat
  apply h20
  linear_combination -hfermat

theorem commonSource_square_mul_sqrt_neg_one_nonsquare_mod_eight {p : ℕ} [Fact p.Prime]
    (hp8 : p % 8 = 5) {n i : ZMod p} (hn : IsSquare n) (hn0 : n ≠ 0)
    (hi : i ^ 2 = -1) : ¬ IsSquare (n * i) := by
  intro hs
  apply commonSource_sqrt_neg_one_nonsquare_mod_eight hp8 hi
  simpa [mul_div_cancel_left₀ _ hn0] using hs.div hn

theorem commonSource_sqrt_neg_one_add_one_ne_zero {K : Type*} [Field K]
    (h20 : (2 : K) ≠ 0) {i : K} (hi : i ^ 2 = -1) : i + 1 ≠ 0 := by
  intro h
  have hi1 : i = -1 := by linear_combination h
  rw [hi1] at hi
  apply h20
  linear_combination hi

theorem commonSource_odd_cyclic_residue_identity {K : Type*} [Field K]
    (h20 : (2 : K) ≠ 0) {n i : K} (hn0 : n ≠ 0) (hi : i ^ 2 = -1) :
    (n * i + n * i) / (2 * (n * i + n)) = (1 + i) / 2 := by
  have hi1 := commonSource_sqrt_neg_one_add_one_ne_zero h20 hi
  have hd : n * i + n ≠ 0 := by
    simpa only [mul_add, mul_one] using mul_ne_zero hn0 hi1
  apply (div_eq_div_iff (mul_ne_zero h20 hd) h20).mpr
  linear_combination -2 * n * hi

theorem odd_cyclic_residue_cleared_identity {K : Type*} [Field K]
    (h20 : (2 : K) ≠ 0) {n i : K} (hn0 : n ≠ 0) (hi : i ^ 2 = -1) :
    ((n * i + n * i) * (2 * (n * i + n))) / (2 * (n * i + n)) ^ 2 =
      (1 + i) / 2 := by
  have hi1 := commonSource_sqrt_neg_one_add_one_ne_zero h20 hi
  have hd : n * i + n ≠ 0 := by
    simpa only [mul_add, mul_one] using mul_ne_zero hn0 hi1
  calc
    _ = (n * i + n * i) / (2 * (n * i + n)) := by field_simp
    _ = _ := commonSource_odd_cyclic_residue_identity h20 hn0 hi

/-- The exact common-source return residue when the two coordinates reduce
to the same cyclic order-four coordinate. The statement includes integrality
of the actual completed-field quotient. -/
theorem commonSource_odd_cyclic_residue {p : ℕ} [Fact p.Prime]
    (a c n : ℤ_[p]) (i : ZMod p) (h20 : (2 : ZMod p) ≠ 0)
    (hn : PadicInt.toZMod n ≠ 0) (hi : i ^ 2 = -1)
    (ha : PadicInt.toZMod a = PadicInt.toZMod n * i)
    (hc : PadicInt.toZMod c = PadicInt.toZMod n * i) :
    ∃ h : ‖((a : ℚ_[p]) + (c : ℚ_[p])) / (2 * ((c : ℚ_[p]) + (n : ℚ_[p])))‖ ≤ 1,
      padicResidue (((a : ℚ_[p]) + (c : ℚ_[p])) / (2 * ((c : ℚ_[p]) + (n : ℚ_[p])))) h =
        (1 + i) / 2 := by
  have hi1 := commonSource_sqrt_neg_one_add_one_ne_zero h20 hi
  have hd : PadicInt.toZMod (2 * (c + n)) ≠ 0 := by
    simp only [map_mul, map_add, map_ofNat, hc]
    apply mul_ne_zero h20
    simpa only [mul_add, mul_one] using mul_ne_zero hn hi1
  obtain ⟨h, hred⟩ := commonSource_ratio_integral_residue (a + c) (2 * (c + n)) hd
  refine ⟨h, hred.trans ?_⟩
  simpa only [map_mul, map_add, map_ofNat, ha, hc] using
    commonSource_odd_cyclic_residue_identity h20 hn hi

/-- A wrong square class of the cyclic unit residue obstructs the actual
return value, at every depth of the corresponding residue disks. -/
theorem commonSource_odd_cyclic_nonsquare {p : ℕ} [Fact p.Prime]
    (a c n : ℤ_[p]) (i : ZMod p) (h20 : (2 : ZMod p) ≠ 0)
    (hn : PadicInt.toZMod n ≠ 0) (hi : i ^ 2 = -1)
    (ha : PadicInt.toZMod a = PadicInt.toZMod n * i)
    (hc : PadicInt.toZMod c = PadicInt.toZMod n * i)
    (hwrong : ¬ IsSquare ((1 + i) / 2)) :
    ¬ IsSquare (((a : ℚ_[p]) + (c : ℚ_[p])) / (2 * ((c : ℚ_[p]) + (n : ℚ_[p])))) := by
  obtain ⟨h, hred⟩ := commonSource_odd_cyclic_residue a c n i h20 hn hi ha hc
  intro hs
  apply hwrong
  rw [← hred]
  exact padic_residue_isSquare_of_isSquare _ h hs

/-- The opposite cyclic coordinate has the other exact return residue. -/
theorem commonSource_odd_cyclic_neg_residue {p : ℕ} [Fact p.Prime]
    (a c n : ℤ_[p]) (i : ZMod p) (h20 : (2 : ZMod p) ≠ 0)
    (hn : PadicInt.toZMod n ≠ 0) (hi : i ^ 2 = -1)
    (ha : PadicInt.toZMod a = -(PadicInt.toZMod n * i))
    (hc : PadicInt.toZMod c = -(PadicInt.toZMod n * i)) :
    ∃ h : ‖((a : ℚ_[p]) + (c : ℚ_[p])) / (2 * ((c : ℚ_[p]) + (n : ℚ_[p])))‖ ≤ 1,
      padicResidue (((a : ℚ_[p]) + (c : ℚ_[p])) / (2 * ((c : ℚ_[p]) + (n : ℚ_[p])))) h =
        (1 - i) / 2 := by
  simpa only [mul_neg, sub_eq_add_neg] using
    commonSource_odd_cyclic_residue a c n (-i) h20 hn
      (by simpa using hi) (by simpa using ha) (by simpa using hc)

/-- Nonsquare obstruction for the opposite cyclic coordinate. -/
theorem commonSource_odd_cyclic_neg_nonsquare {p : ℕ} [Fact p.Prime]
    (a c n : ℤ_[p]) (i : ZMod p) (h20 : (2 : ZMod p) ≠ 0)
    (hn : PadicInt.toZMod n ≠ 0) (hi : i ^ 2 = -1)
    (ha : PadicInt.toZMod a = -(PadicInt.toZMod n * i))
    (hc : PadicInt.toZMod c = -(PadicInt.toZMod n * i))
    (hwrong : ¬ IsSquare ((1 - i) / 2)) :
    ¬ IsSquare (((a : ℚ_[p]) + (c : ℚ_[p])) / (2 * ((c : ℚ_[p]) + (n : ℚ_[p])))) := by
  obtain ⟨h, hred⟩ := commonSource_odd_cyclic_neg_residue a c n i h20 hn hi ha hc
  intro hs
  apply hwrong
  rw [← hred]
  exact padic_residue_isSquare_of_isSquare _ h hs

/-- The cyclic return is a unit throughout its residue disk. -/
theorem commonSource_odd_cyclic_norm_one {p : ℕ} [Fact p.Prime]
    (a c n : ℤ_[p]) (i : ZMod p) (h20 : (2 : ZMod p) ≠ 0)
    (hn : PadicInt.toZMod n ≠ 0) (hi : i ^ 2 = -1)
    (ha : PadicInt.toZMod a = PadicInt.toZMod n * i)
    (hc : PadicInt.toZMod c = PadicInt.toZMod n * i) :
    ‖((a : ℚ_[p]) + (c : ℚ_[p])) /
      (2 * ((c : ℚ_[p]) + (n : ℚ_[p])))‖ = 1 := by
  obtain ⟨h, hred⟩ := commonSource_odd_cyclic_residue a c n i h20 hn hi ha hc
  apply (padicInt_norm_eq_one_iff_residue_ne_zero (padicIntegral _ h)).mpr
  change padicResidue _ h ≠ 0
  rw [hred]
  apply div_ne_zero _ h20
  simpa only [add_comm] using commonSource_sqrt_neg_one_add_one_ne_zero h20 hi

end FourCorner

#print axioms FourCorner.commonSource_ratio_nonsquare_of_residue
#print axioms FourCorner.commonSource_both_plus_nonsquare_mod_eight
#print axioms FourCorner.commonSource_both_minus_nonsquare_mod_eight
#print axioms FourCorner.commonSource_odd_cyclic_residue
#print axioms FourCorner.commonSource_odd_cyclic_neg_residue
#print axioms FourCorner.commonSource_odd_cyclic_nonsquare
#print axioms FourCorner.commonSource_odd_cyclic_neg_nonsquare
#print axioms FourCorner.commonSource_odd_cyclic_norm_one
