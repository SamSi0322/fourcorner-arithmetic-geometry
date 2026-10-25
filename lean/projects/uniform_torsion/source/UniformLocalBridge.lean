import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import EllipticCurves.Mathlib.EllipticCurvePoint
import OddTorsion

/-! The actual rational-to-local point map and a pole criterion for the first
formal-group filtration. No assumption of good reduction is used. -/

namespace FourCorner.UniformTorsion.LocalBridge

open IsDedekindDomain WeierstrassCurve.Affine WithZero

noncomputable def primeTwo : HeightOneSpectrum ℤ :=
  (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨2, Nat.prime_two⟩

theorem primeTwo_natGenerator : Rat.HeightOneSpectrum.natGenerator primeTwo = 2 := by
  exact congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply ⟨2, Nat.prime_two⟩)

noncomputable abbrev LocalField := primeTwo.adicCompletion ℚ
noncomputable abbrev LocalIntegers := primeTwo.adicCompletionIntegers ℚ

noncomputable def localFieldEquivPadic : LocalField ≃A[ℚ] ℚ_[2] :=
  (Padic.adicCompletionEquiv ℤ ⟨2, Nat.prime_two⟩).symm

noncomputable local instance : DecidableEq LocalField := Classical.decEq _

theorem primeTwo_valuation_equiv :
    (primeTwo.valuation ℚ).IsEquiv (Rat.padicValuation 2) := by
  have h := Rat.HeightOneSpectrum.valuation_equiv_padicValuation primeTwo
  have hp : Rat.HeightOneSpectrum.primesEquiv primeTwo = ⟨2, Nat.prime_two⟩ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply ⟨2, Nat.prime_two⟩
  simpa only [hp] using h

theorem primeTwo_one_lt_valuation {x : ℚ} (hx : padicValRat 2 x < 0) :
    1 < primeTwo.valuation ℚ x := by
  have hx0 : x ≠ 0 := by intro h; subst x; simp at hx
  have hp : 1 < Rat.padicValuation 2 x := by
    change 1 < if x = 0 then 0 else exp (-padicValRat 2 x)
    rw [if_neg hx0, ← exp_zero, exp_lt_exp]
    omega
  exact primeTwo_valuation_equiv.one_lt_iff_one_lt.mpr hp

theorem two_mem_primeTwo : (2 : ℤ) ∈ primeTwo.asIdeal := by
  have hp : Rat.padicValuation 2 (2 : ℚ) < 1 := by
    have hself : Rat.padicValuation 2 (2 : ℚ) = exp (-1 : ℤ) :=
      Rat.padicValuation_self 2
    rw [hself, ← exp_zero, exp_lt_exp]
    norm_num
  have hv : primeTwo.valuation ℚ (2 : ℚ) < 1 := by
    exact primeTwo_valuation_equiv.lt_one_iff_lt_one.mpr hp
  exact (primeTwo.valuation_lt_one_iff_mem (K := ℚ) (2 : ℤ)).mp (by simpa using hv)

noncomputable def completionPointMap (W : WeierstrassCurve.Affine ℚ) :
    W.Point →+ (W ⁄ LocalField).toAffine.Point := W.pointMap LocalField

theorem completionPointMap_injective (W : WeierstrassCurve.Affine ℚ) :
    Function.Injective (completionPointMap W) := W.pointMap_injective LocalField

noncomputable def localIntegralModel (W₀ : WeierstrassCurve ℤ) :
    WeierstrassCurve LocalIntegers := W₀.map (algebraMap ℤ LocalIntegers)

theorem localIntegralModel_map {W₀ : WeierstrassCurve ℤ}
    {W : WeierstrassCurve.Affine ℚ} (hW : W₀.map (algebraMap ℤ ℚ) = W) :
    (localIntegralModel W₀).map (algebraMap LocalIntegers LocalField) =
      (W ⁄ LocalField).toAffine := by
  rw [← hW]
  change (W₀.map (algebraMap ℤ LocalIntegers)).map (algebraMap LocalIntegers LocalField) =
    (W₀.map (algebraMap ℤ ℚ)).map (algebraMap ℚ LocalField)
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map,
    ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

variable {W₀ : WeierstrassCurve ℤ} {W : WeierstrassCurve.Affine ℚ}
  [W.IsElliptic] (hW : W₀.map (algebraMap ℤ ℚ) = W)

local instance completionCurve_isElliptic : (W ⁄ LocalField).toAffine.IsElliptic :=
  inferInstanceAs ((W.map (algebraMap ℚ LocalField)).IsElliptic)

/-- A negative rational 2-adic x-valuation puts the actual mapped point in G1.
The even-pole bound follows from the equation and the integral coefficients. -/
theorem completionPoint_some_mem_filtration_of_negative {x y : ℚ}
    (h : W.Nonsingular x y) (hx : padicValRat 2 x < 0) :
    completionPointMap W (.some x y h) ∈ filtration (localIntegralModel_map hW) 0 := by
  change W.pointMap LocalField (.some x y h) ∈ _
  rw [pointMap_some, some_mem_filtration]
  change exp (2 : ℤ) ≤ Valued.v (algebraMap ℚ LocalField x)
  have hxv : 1 < Valued.v (algebraMap ℚ LocalField x) := by
    have heq : Valued.v (algebraMap ℚ LocalField x) = primeTwo.valuation ℚ x :=
      primeTwo.valuedAdicCompletion_eq_valuation' x
    rw [heq]
    exact primeTwo_one_lt_valuation hx
  by_contra hnot
  exact (not_le_of_gt hxv)
    (integral_of_not_mem (localIntegralModel_map hW)
      (W.pointMap_nonsingular LocalField h).1 hnot).1

theorem completionPoint_some_mem_filtration_of_pole {x y : ℚ}
    (h : W.Nonsingular x y) (hx : padicValRat 2 x ≤ -2) :
    completionPointMap W (.some x y h) ∈ filtration (localIntegralModel_map hW) 0 :=
  completionPoint_some_mem_filtration_of_negative hW h (by omega)

/-- Transfer the accepted local odd-torsion theorem back through the injective
rational point map. Membership is supplied by the pole theorem when applicable. -/
theorem eq_zero_of_odd_of_four_image_mem {n : ℕ} (hn : Odd n) {P : W.Point}
    (hfour : 4 • completionPointMap W P ∈ filtration (localIntegralModel_map hW) 0)
    (hkill : n • P = 0) : P = 0 := by
  have hkillLocal : n • completionPointMap W P = 0 := by
    rw [← map_nsmul, hkill, map_zero]
  have hz : completionPointMap W P = 0 :=
    eq_zero_of_odd_nsmul_of_four_nsmul_mem_filtration two_mem_primeTwo hn hfour hkillLocal
  apply completionPointMap_injective W
  simpa only [map_zero] using hz

/-- Named interface for a direct proof that four times the mapped point belongs
to the first filtration subgroup. -/
theorem eq_zero_of_odd_of_four_map_mem_filtration {n : ℕ} (hn : Odd n) {P : W.Point}
    (hfour : 4 • completionPointMap W P ∈ filtration (localIntegralModel_map hW) 0)
    (hkill : n • P = 0) : P = 0 :=
  eq_zero_of_odd_of_four_image_mem hW hn hfour hkill

include hW in
/-- A concrete rational pole at four times an odd-torsion point forces it to
vanish; no formal-group membership is assumed in the hypotheses. -/
theorem eq_zero_of_odd_of_four_eq_pole {n : ℕ} (hn : Odd n) {P : W.Point}
    (hkill : n • P = 0) {x y : ℚ} (h : W.Nonsingular x y)
    (hfour : 4 • P = .some x y h) (hx : padicValRat 2 x ≤ -2) : P = 0 := by
  apply eq_zero_of_odd_of_four_image_mem hW hn ?_ hkill
  rw [← map_nsmul, hfour]
  exact completionPoint_some_mem_filtration_of_pole hW h hx

include hW in
/-- A rational zero-or-pole alternative for four times the point is enough:
the local filtration membership is a proved consequence of that alternative. -/
theorem eq_zero_of_odd_of_four_zero_or_pole {n : ℕ} (hn : Odd n) {P : W.Point}
    (hkill : n • P = 0)
    (hfour : 4 • P = 0 ∨ ∃ (x y : ℚ) (h : W.Nonsingular x y),
      4 • P = .some x y h ∧ padicValRat 2 x ≤ -2) : P = 0 := by
  apply eq_zero_of_odd_of_four_image_mem hW hn ?_ hkill
  rw [← map_nsmul]
  rcases hfour with hz | ⟨x, y, h, heq, hx⟩
  · rw [hz, map_zero]
    exact zero_mem_filtration
  · rw [heq]
    exact completionPoint_some_mem_filtration_of_pole hW h hx

#print axioms completionPointMap_injective
#print axioms completionPoint_some_mem_filtration_of_pole
#print axioms eq_zero_of_odd_of_four_map_mem_filtration
#print axioms eq_zero_of_odd_of_four_eq_pole
#print axioms eq_zero_of_odd_of_four_zero_or_pole

end FourCorner.UniformTorsion.LocalBridge
