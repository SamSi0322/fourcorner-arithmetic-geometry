import GroupInterface
import FieldGroup
import RationalPrimeValuation
import EllipticCurves.ReductionAtPrime
import FourCorner.CommonRootPadicResidue
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace FourCorner.CommonSource
open IsDedekindDomain WeierstrassCurve.Affine

/-- The literal integral model of the congruent-number elliptic curve. -/
def integralCurve (n : ℤ) : WeierstrassCurve ℤ := ⟨0, 0, 0, -(n ^ 2), 0⟩

/-- The actual nonsingular finite-field point group of the integral model. -/
abbrev residueCurve (n : ℤ) (q : ℕ) : WeierstrassCurve.Affine (ZMod q) :=
  ((integralCurve n).map (algebraMap ℤ (ZMod q))).toAffine

abbrev ResiduePoint (n : ℤ) (q : ℕ) := (residueCurve n q).Point

lemma integralCurve_map (n : ℤ) :
    (integralCurve n).map (algebraMap ℤ ℚ) = congruentCurve (n : ℚ) := by
  ext <;> simp [integralCurve, congruentCurve, WeierstrassCurve.map]

lemma residueCurve_discriminant (n : ℤ) (q : ℕ) :
    (residueCurve n q).Δ = 64 * (n : ZMod q) ^ 6 := by
  simp [residueCurve, integralCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    WeierstrassCurve.map, WeierstrassCurve.toAffine]
  ring

variable {q : ℕ} [Fact q.Prime]

lemma integer_ne_zero_of_good {n : ℤ} (hnq : (n : ZMod q) ≠ 0) : n ≠ 0 := by
  intro hn
  apply hnq
  simp [hn]

lemma rational_ne_zero_of_good {n : ℤ} (hnq : (n : ZMod q) ≠ 0) : (n : ℚ) ≠ 0 := by
  exact_mod_cast integer_ne_zero_of_good hnq

/-- The hypothesis that the prime does not divide `2n` proves genuine good reduction. -/
lemma residueCurve_isElliptic (n : ℤ) (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0) :
    (residueCurve n q).IsElliptic := by
  apply (WeierstrassCurve.isElliptic_iff _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [residueCurve_discriminant]
  apply mul_ne_zero _ (pow_ne_zero _ hnq)
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 q).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact (Fact.out : Nat.Prime q).ne_one h1
    · exact hq2 h2
  have h64 : (64 : ZMod q) = 2 ^ 6 := by norm_num
  rw [h64]
  exact pow_ne_zero _ h2

lemma quotientCurve_isElliptic (n : ℤ) (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0) :
    (redCurve (primeIdeal q) (integralCurve n)).IsElliptic := by
  apply (WeierstrassCurve.isElliptic_iff _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have heq := congrArg (residueEquiv q) hz
  rw [map_zero] at heq
  have hgood := (residueCurve_isElliptic n hq2 hnq).1
  apply (isUnit_iff_ne_zero.mp hgood)
  change (residueEquiv q) (((integralCurve n).map
    (algebraMap ℤ (ℤ ⧸ (primeIdeal q).asIdeal))).Δ) = 0 at heq
  simpa [residueCurve, WeierstrassCurve.map_Δ] using heq

/-- Canonical reduction: the accepted good-reduction homomorphism, followed only by
`ℤ/(q) ≃ ZMod q`. The codomain is Mathlib's actual elliptic-curve group. -/
def reduce (n : ℤ) (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0) :
    Point (n : ℚ) →+ ResiduePoint n q := by
  letI : (congruentCurve (n : ℚ)).toAffine.IsElliptic :=
    isElliptic (rational_ne_zero_of_good hnq)
  letI : (redCurve (primeIdeal q) (integralCurve n)).IsElliptic :=
    quotientCurve_isElliptic n hq2 hnq
  letI : DecidableEq (ℤ ⧸ (primeIdeal q).asIdeal) := Classical.decEq _
  exact (WeierstrassCurve.Affine.Point.map (W' := (integralCurve n).toAffine)
      (residueEquiv q).toIntAlgEquiv.toAlgHom).comp
    (redHom (primeIdeal q) (E := (congruentCurve (n : ℚ)).toAffine)
      (W₀ := integralCurve n) (integralCurve_map n))

/-- Affine coordinates in the actual reduced point group. -/
def residueCoordinates {n : ℤ} : ResiduePoint n q → Option (ZMod q × ZMod q)
  | .zero => none
  | .some x y _ => some (x, y)

@[simp] lemma residueCoordinates_zero (n : ℤ) :
    residueCoordinates (0 : ResiduePoint n q) = none := rfl

lemma residueCoordinates_injective {n : ℤ} :
    Function.Injective (@residueCoordinates q n) := by
  intro P Q h
  cases P <;> cases Q <;> simp_all [residueCoordinates]

lemma reduce_finitePoint_of_not_integral {n : ℤ} (hq2 : q ≠ 2)
    (hnq : (n : ZMod q) ≠ 0) {x y : ℚ}
    (hcurve : CongruentEquation (n : ℚ) x y)
    (hx : ¬ (primeIdeal q).valuation ℚ x ≤ 1) :
    reduce n hq2 hnq (finitePoint (rational_ne_zero_of_good hnq) hcurve) = 0 := by
  classical
  letI : (redCurve (primeIdeal q) (integralCurve n)).IsElliptic :=
    quotientCurve_isElliptic n hq2 hnq
  change WeierstrassCurve.Affine.Point.map (W' := (integralCurve n).toAffine)
    (residueEquiv q).toIntAlgEquiv.toAlgHom
    (red (primeIdeal q) (integralCurve_map n)
      (.some x y (nonsingular (rational_ne_zero_of_good hnq) hcurve))) = 0
  rw [red_some_of_not_le _ _ hx, map_zero]

lemma integral_ordinate {n : ℤ} {x y : ℚ}
    (hcurve : CongruentEquation (n : ℚ) x y)
    (hx : (primeIdeal q).valuation ℚ x ≤ 1) :
    (primeIdeal q).valuation ℚ y ≤ 1 :=
  valuation_le_one_of_equation (primeIdeal q) (integralCurve_map n)
    ((congruentEquation_iff_weierstrass _ _ _).mp hcurve) hx

lemma reduce_finitePoint_coordinates {n : ℤ} (hq2 : q ≠ 2)
    (hnq : (n : ZMod q) ≠ 0) {x y : ℚ}
    (hcurve : CongruentEquation (n : ℚ) x y)
    (hx : (primeIdeal q).valuation ℚ x ≤ 1) :
    residueCoordinates (reduce n hq2 hnq
      (finitePoint (rational_ne_zero_of_good hnq) hcurve)) =
      some ((residueEquiv q) (HeightOneSpectrum.residueHom (primeIdeal q) ⟨x, hx⟩),
        (residueEquiv q) (HeightOneSpectrum.residueHom (primeIdeal q)
          ⟨y, integral_ordinate hcurve hx⟩)) := by
  classical
  letI : (redCurve (primeIdeal q) (integralCurve n)).IsElliptic :=
    quotientCurve_isElliptic n hq2 hnq
  change residueCoordinates (WeierstrassCurve.Affine.Point.map
    (W' := (integralCurve n).toAffine) (residueEquiv q).toIntAlgEquiv.toAlgHom
    (red (primeIdeal q) (integralCurve_map n)
      (.some x y (nonsingular (rational_ne_zero_of_good hnq) hcurve)))) = _
  rw [red_some_of_le _ _ hx]
  rfl

/-- Integral affine points reduce to their actual `q`-adic coordinate residues. -/
lemma reduce_finitePoint_padic_coordinates {n : ℤ} (hq2 : q ≠ 2)
    (hnq : (n : ZMod q) ≠ 0) {x y : ℚ}
    (hcurve : CongruentEquation (n : ℚ) x y)
    (hx : (primeIdeal q).valuation ℚ x ≤ 1) :
    residueCoordinates (reduce n hq2 hnq
      (finitePoint (rational_ne_zero_of_good hnq) hcurve)) =
      some (PadicInt.toZMod (rationalIntegral q x hx),
        PadicInt.toZMod (rationalIntegral q y (integral_ordinate hcurve hx))) := by
  rw [reduce_finitePoint_coordinates hq2 hnq hcurve hx]
  rw [residue_compatibility, residue_compatibility]

/-- A rational affine point reduces to infinity exactly when its abscissa has a pole. -/
lemma reduce_finitePoint_eq_zero_iff {n : ℤ} (hq2 : q ≠ 2)
    (hnq : (n : ZMod q) ≠ 0) {x y : ℚ}
    (hcurve : CongruentEquation (n : ℚ) x y) :
    reduce n hq2 hnq (finitePoint (rational_ne_zero_of_good hnq) hcurve) = 0 ↔
      1 < ‖(x : ℚ_[q])‖ := by
  constructor
  · intro hzero
    by_contra hx
    have hxv := (valuation_le_one_iff_norm q x).mpr (le_of_not_gt hx)
    have hc := reduce_finitePoint_coordinates hq2 hnq hcurve hxv
    rw [hzero, residueCoordinates_zero] at hc
    contradiction
  · intro hx
    apply reduce_finitePoint_of_not_integral hq2 hnq hcurve
    intro hxv
    exact not_le_of_gt hx ((valuation_le_one_iff_norm q x).mp hxv)

/-- Any finite reduction supplies the actual integral abscissa and ordinate. -/
lemma integral_coordinates_of_reduction_some {n : ℤ} (hq2 : q ≠ 2)
    (hnq : (n : ZMod q) ≠ 0) {x y : ℚ}
    (hcurve : CongruentEquation (n : ℚ) x y) {u v : ZMod q}
    (hred : residueCoordinates (reduce n hq2 hnq
      (finitePoint (rational_ne_zero_of_good hnq) hcurve)) = some (u,v)) :
    ∃ hx : (primeIdeal q).valuation ℚ x ≤ 1,
      PadicInt.toZMod (rationalIntegral q x hx) = u ∧
      PadicInt.toZMod (rationalIntegral q y (integral_ordinate hcurve hx)) = v := by
  have hx : (primeIdeal q).valuation ℚ x ≤ 1 := by
    by_contra hx
    rw [reduce_finitePoint_of_not_integral hq2 hnq hcurve hx,
      residueCoordinates_zero] at hred
    contradiction
  refine ⟨hx, ?_⟩
  rw [reduce_finitePoint_padic_coordinates hq2 hnq hcurve hx] at hred
  exact Prod.mk.inj (Option.some.inj hred)

/-- The integral parameter is a unit in the actual completed field. -/
lemma parameter_norm_eq_one (n : ℤ) (hnq : (n : ZMod q) ≠ 0) :
    ‖(n : ℚ_[q])‖ = 1 := by
  apply padicInt_norm_coe_eq_one_of_residue_ne_zero (n : ℤ_[q])
  simpa using hnq

lemma residueCurve_eq_fieldCurve (n : ℤ) :
    residueCurve n q = (OverField.curve (n : ZMod q)).toAffine := by
  ext <;> simp [residueCurve, integralCurve, OverField.curve, WeierstrassCurve.map,
    WeierstrassCurve.toAffine]

/-- The three literal finite-field points at the roots of the reduced cubic. -/
def residueT0 (n : ℤ) (hnq : (n : ZMod q) ≠ 0) : ResiduePoint n q :=
  .some 0 0 (by
    rw [residueCurve_eq_fieldCurve]
    exact OverField.nonsingular_zero _ hnq)

def residueTplus (n : ℤ) (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0) :
    ResiduePoint n q := by
  letI := residueCurve_isElliptic n hq2 hnq
  exact .some (n : ZMod q) 0 ((residueCurve n q).equation_iff_nonsingular.mp (by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [residueCurve, integralCurve, WeierstrassCurve.map, WeierstrassCurve.toAffine]
    ring))

def residueTminus (n : ℤ) (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0) :
    ResiduePoint n q := by
  letI := residueCurve_isElliptic n hq2 hnq
  exact .some (-(n : ZMod q)) 0 ((residueCurve n q).equation_iff_nonsingular.mp (by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [residueCurve, integralCurve, WeierstrassCurve.map, WeierstrassCurve.toAffine]
    ring))

@[simp] lemma residueCoordinates_T0 (n : ℤ) (hnq : (n : ZMod q) ≠ 0) :
    residueCoordinates (residueT0 n hnq) = some (0,0) := rfl

@[simp] lemma residueCoordinates_Tplus (n : ℤ) (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0) :
    residueCoordinates (residueTplus n hq2 hnq) = some ((n : ZMod q),0) := rfl

@[simp] lemma residueCoordinates_Tminus (n : ℤ) (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0) :
    residueCoordinates (residueTminus n hq2 hnq) = some (-(n : ZMod q),0) := rfl

lemma rationalIntegral_int (a : ℤ) (ha : (primeIdeal q).valuation ℚ (a : ℚ) ≤ 1) :
    rationalIntegral q (a : ℚ) ha = (a : ℤ_[q]) := by
  apply PadicInt.ext
  simp

lemma valuation_int_le_one (a : ℤ) : (primeIdeal q).valuation ℚ (a : ℚ) ≤ 1 := by
  apply (valuation_le_one_iff_norm q _).mpr
  rw [Rat.cast_intCast]
  exact (a : ℤ_[q]).property

@[simp] lemma reduce_T0 (n : ℤ) (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0) :
    reduce n hq2 hnq (T0 (n : ℚ) (rational_ne_zero_of_good hnq)) = residueT0 n hnq := by
  apply residueCoordinates_injective
  rw [T0, reduce_finitePoint_padic_coordinates hq2 hnq _ (by simp), residueCoordinates_T0]
  simp [rationalIntegral]

@[simp] lemma reduce_Tplus (n : ℤ) (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0) :
    reduce n hq2 hnq (Tplus (n : ℚ) (rational_ne_zero_of_good hnq)) =
      residueTplus n hq2 hnq := by
  apply residueCoordinates_injective
  rw [Tplus, reduce_finitePoint_padic_coordinates hq2 hnq _ (valuation_int_le_one n),
    residueCoordinates_Tplus, rationalIntegral_int]
  simp [rationalIntegral]

@[simp] lemma reduce_Tminus (n : ℤ) (hq2 : q ≠ 2) (hnq : (n : ZMod q) ≠ 0) :
    reduce n hq2 hnq (Tminus (n : ℚ) (rational_ne_zero_of_good hnq)) =
      residueTminus n hq2 hnq := by
  apply residueCoordinates_injective
  rw [Tminus, reduce_finitePoint_padic_coordinates hq2 hnq _ (by
    simpa using valuation_int_le_one (q := q) (-n)), residueCoordinates_Tminus]
  have hh := rationalIntegral_int (q := q) (-n)
  simp only [Int.cast_neg] at hh
  rw [hh (by simpa using valuation_int_le_one (q := q) (-n))]
  simp [rationalIntegral]

/-- The norm disk of `T0` is forced by reduction in the genuine group. -/
lemma norm_lt_one_of_reduce_T0 {n : ℤ} (hq2 : q ≠ 2)
    (hnq : (n : ZMod q) ≠ 0) {x y : ℚ}
    (hcurve : CongruentEquation (n : ℚ) x y)
    (hred : reduce n hq2 hnq (finitePoint (rational_ne_zero_of_good hnq) hcurve) =
      residueT0 n hnq) : ‖(x : ℚ_[q])‖ < 1 ∧ ‖(y : ℚ_[q])‖ < 1 := by
  have hc := congrArg residueCoordinates hred
  rw [residueCoordinates_T0] at hc
  obtain ⟨hx, hx0, hy0⟩ := integral_coordinates_of_reduction_some hq2 hnq hcurve hc
  constructor
  · exact (padicInt_norm_lt_one_iff_residue_zero (rationalIntegral q x hx)).mpr hx0
  · exact (padicInt_norm_lt_one_iff_residue_zero
      (rationalIntegral q y (integral_ordinate hcurve hx))).mpr hy0

end FourCorner.CommonSource
