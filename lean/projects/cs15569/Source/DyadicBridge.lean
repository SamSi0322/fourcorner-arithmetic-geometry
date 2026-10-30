import GroupInterface
import EllipticCurves.WeierstrassFormalGroup.Filtration
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Tactic

noncomputable section
namespace FourCorner.CommonSource
open IsDedekindDomain WithZero

/-- The rational prime two, viewed as a height-one prime of the integers. -/
def dyadicPrime : HeightOneSpectrum ℤ :=
  (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨2, Nat.prime_two⟩

abbrev DyadicField := dyadicPrime.adicCompletion ℚ
abbrev DyadicIntegers := dyadicPrime.adicCompletionIntegers ℚ
local instance : DecidableEq DyadicField := Classical.decEq _

lemma dyadicPrime_asIdeal : dyadicPrime.asIdeal = Ideal.span {(2 : ℤ)} := by
  have h : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ := by
    ext x
    simp
  change (Ideal.span {(2 : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
  rw [h]
  change Ideal.map (RingHom.id ℤ) _ = _
  exact Ideal.map_id _

lemma dyadicPrime_two : dyadicPrime.valuation ℚ (2 : ℚ) = exp (-1 : ℤ) := by
  rw [show (2 : ℚ) = algebraMap ℤ ℚ 2 by simp,
    dyadicPrime.valuation_of_algebraMap, dyadicPrime.intValuation_eq_exp_neg_multiplicity (by norm_num),
    dyadicPrime_asIdeal]
  rw [multiplicity_self]
  norm_num


lemma dyadic_valuation_rat (x : ℚ) (hx : x ≠ 0) :
    dyadicPrime.valuation ℚ x = exp (-padicValRat 2 x) := by
  have he : (dyadicPrime.valuation ℚ).IsEquiv (Rat.padicValuation 2) := by
    have h := Rat.HeightOneSpectrum.valuation_equiv_padicValuation dyadicPrime
    have hprime : (Rat.HeightOneSpectrum.primesEquiv (R := ℤ) dyadicPrime).val = 2 :=
      congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply _)
    simpa only [hprime] using h
  have hp : Rat.padicValuation 2 x =
      Rat.padicValuation 2 ((2 : ℚ) ^ padicValRat 2 x) := by
    rw [map_zpow₀, show Rat.padicValuation 2 (2 : ℚ) = exp (-1 : ℤ) from
      Rat.padicValuation_self 2, ← exp_zsmul]
    simp [Rat.padicValuation, hx]
  have h := he.eq_iff.mpr hp
  rw [map_zpow₀, dyadicPrime_two, ← exp_zsmul] at h
  simpa using h

/-- The integral congruent-number model over the dyadic valuation ring. -/
def dyadicModel (n : ℤ) : WeierstrassCurve DyadicIntegers :=
  ⟨0, 0, 0, -(n : DyadicIntegers)^2, 0⟩

/-- The rational curve after base change to the dyadic completion. -/
def dyadicCurve (n : ℤ) : WeierstrassCurve.Affine DyadicField :=
  (congruentCurve (n : ℚ)).toAffine.baseChange DyadicField

lemma dyadic_model_eq (n : ℤ) :
    (dyadicModel n).map (algebraMap DyadicIntegers DyadicField) = dyadicCurve n := by
  ext <;> simp [dyadicModel, dyadicCurve, congruentCurve, WeierstrassCurve.toAffine,
    WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange]


lemma dyadicCurve_isElliptic {n : ℤ} (hn : n ≠ 0) : (dyadicCurve n).IsElliptic := by
  let : (congruentCurve (n : ℚ)).IsElliptic := isElliptic (by exact_mod_cast hn)
  change ((congruentCurve (n : ℚ)).map (algebraMap ℚ DyadicField)).IsElliptic
  infer_instance

/-- The actual field-base-change map on the rational elliptic-curve group. -/
def rationalToDyadic (n : ℤ) : Point (n : ℚ) →+ (dyadicCurve n).Point := by
  classical
  let f : ℚ →+* DyadicField := algebraMap ℚ DyadicField
  let W := (congruentCurve (n : ℚ)).toAffine
  let g : W.Point → (dyadicCurve n).Point := fun P => match P with
    | .zero => .zero
    | .some x y h => .some (f x) (f y) ((W.map_nonsingular (f := f) f.injective x y).mpr h)
  refine { toFun := g, map_zero' := rfl, map_add' := ?_ }
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
  · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.left hxy.right]
    change 0 = WeierstrassCurve.Affine.Point.some _ _ _ +
      WeierstrassCurve.Affine.Point.some _ _ _
    exact (WeierstrassCurve.Affine.Point.add_of_Y_eq (W := W.map f) (congr_arg f hxy.left) (by
      rw [hxy.right, W.map_negY])).symm
  · simp only [WeierstrassCurve.Affine.Point.add_some hxy, g]
    simpa only [← W.map_addX, ← W.map_addY, ← W.map_slope] using!
      (WeierstrassCurve.Affine.Point.add_some (W := W.map f) fun h =>
        hxy ⟨f.injective h.1, f.injective (W.map_negY f _ _ ▸ h).2⟩).symm

@[simp] lemma rationalToDyadic_some (n : ℤ) (x y : ℚ)
    (h : (congruentCurve (n : ℚ)).toAffine.Nonsingular x y) :
    rationalToDyadic n (.some x y h) = .some (algebraMap ℚ DyadicField x)
      (algebraMap ℚ DyadicField y)
      (((congruentCurve (n : ℚ)).toAffine.map_nonsingular
        (f := algebraMap ℚ DyadicField) (algebraMap ℚ DyadicField).injective x y).mpr h) := rfl

/-- The rational points in the actual dyadic formal neighborhood `E_(k+1)`. -/
def Hlevel (n : ℤ) (hn : n ≠ 0) (k : ℕ) : AddSubgroup (Point (n : ℚ)) := by
  classical
  letI := dyadicCurve_isElliptic hn
  exact (WeierstrassCurve.Affine.filtration (dyadic_model_eq n) k).comap (rationalToDyadic n)

/-- The subgroup `H` used in the paper, including the point at infinity. -/
def H (n : ℤ) (hn : n ≠ 0) : AddSubgroup (Point (n : ℚ)) := Hlevel n hn 1

@[simp] lemma zero_mem_Hlevel (n : ℤ) (hn : n ≠ 0) (k : ℕ) :
    (0 : Point (n : ℚ)) ∈ Hlevel n hn k := (Hlevel n hn k).zero_mem

lemma some_mem_Hlevel_iff (n : ℤ) (hn : n ≠ 0) (k : ℕ)
    (x y : ℚ) (h : (congruentCurve (n : ℚ)).toAffine.Nonsingular x y) :
    (.some x y h : Point (n : ℚ)) ∈ Hlevel n hn k ↔
      x ≠ 0 ∧ padicValRat 2 x ≤ -2 * (k + 1) := by
  classical
  change exp (2 * (k + 1) : ℤ) ≤ Valued.v (algebraMap ℚ DyadicField x) ↔ _
  have hval := dyadicPrime.valuedAdicCompletion_eq_valuation' x
  change Valued.v (algebraMap ℚ DyadicField x) = _ at hval
  rw [hval]
  by_cases hx : x = 0
  · subst x
    rw [map_zero]
    simp only [ne_eq, not_true_eq_false, false_and, iff_false]
    exact not_le.mpr exp_pos
  · rw [dyadic_valuation_rat x hx, exp_le_exp]
    constructor
    · intro hh
      exact ⟨hx, by omega⟩
    · rintro ⟨_, hh⟩
      omega

@[simp] lemma some_mem_H_iff (n : ℤ) (hn : n ≠ 0)
    (x y : ℚ) (h : (congruentCurve (n : ℚ)).toAffine.Nonsingular x y) :
    (.some x y h : Point (n : ℚ)) ∈ H n hn ↔ padicValRat 2 x ≤ -4 := by
  rw [H, some_mem_Hlevel_iff]
  change (x ≠ 0 ∧ padicValRat 2 x ≤ -4) ↔ padicValRat 2 x ≤ -4
  constructor
  · exact And.right
  · intro hx
    refine ⟨?_, hx⟩
    intro hx0
    simp [hx0] at hx

end FourCorner.CommonSource
