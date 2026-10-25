import EllipticCurves.ReductionAtPrime
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Torsion
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import FourCorner.NineFlexGroup

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace FourCorner.SmallReduction
open IsDedekindDomain WeierstrassCurve.Affine

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The actual height-one prime ideal (5) of Z. -/
def primeFive : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(5 : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)).mpr
    (Nat.prime_iff_prime_int.mp (by norm_num : Nat.Prime 5))
  ne_bot := by simp

theorem five_mem_prime : (5 : ℤ) ∈ primeFive.asIdeal := by
  change (5 : ℤ) ∈ Ideal.span {(5 : ℤ)}
  simp

theorem five_unramified : (5 : ℤ) ∉ primeFive.asIdeal ^ (5 - 1) := by
  change (5 : ℤ) ∉ Ideal.span {(5 : ℤ)} ^ (5 - 1)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  norm_num

noncomputable abbrev residueFiveEquiv : (ℤ ⧸ primeFive.asIdeal) ≃+* ZMod 5 :=
  Int.quotientSpanNatEquivZMod 5

noncomputable abbrev rationalCurve (W₀ : WeierstrassCurve ℤ) : WeierstrassCurve.Affine ℚ :=
  (W₀.map (algebraMap ℤ ℚ)).toAffine

noncomputable abbrev finiteCurve (W₀ : WeierstrassCurve ℤ) : WeierstrassCurve.Affine (ZMod 5) :=
  (W₀.map (algebraMap ℤ (ZMod 5))).toAffine

/-- Nonvanishing discriminant modulo five establishes actual good reduction. -/
theorem good_reduction_five (W₀ : WeierstrassCurve ℤ)
    (hgood : (finiteCurve W₀).Δ ≠ 0) : (redCurve primeFive W₀).IsElliptic := by
  apply (WeierstrassCurve.isElliptic_iff _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have heq := congrArg residueFiveEquiv hz
  apply hgood
  change (W₀.map (algebraMap ℤ (ZMod 5))).Δ = 0
  change residueFiveEquiv ((W₀.map (algebraMap ℤ (ℤ ⧸ primeFive.asIdeal))).Δ) = 0 at heq
  simpa [WeierstrassCurve.map_Δ] using heq

variable (W₀ : WeierstrassCurve ℤ)
  [(rationalCurve W₀).IsElliptic] [(redCurve primeFive W₀).IsElliptic]

noncomputable local instance : DecidableEq (ℤ ⧸ primeFive.asIdeal) := Classical.decEq _

/-- The residue-field identification is applied to the genuine good-reduction map. -/
noncomputable def reduceFive : (rationalCurve W₀).Point →+ (finiteCurve W₀).Point :=
  (Point.map (W' := W₀.toAffine) residueFiveEquiv.toIntAlgEquiv.toAlgHom).comp
    (redHom primeFive (E := rationalCurve W₀) (W₀ := W₀) rfl)

/-- Good reduction at the unramified odd prime five is injective on the
entire actual rational torsion subgroup, including its five-primary part. -/
theorem reduceFive_torsion_injective :
    Function.Injective (fun P : AddCommGroup.torsion (rationalCurve W₀).Point =>
      reduceFive W₀ P.val) := by
  intro P Q hPQ
  dsimp only at hPQ
  apply Subtype.ext
  apply sub_eq_zero.mp
  have htor : IsOfFinAddOrder (P.val - Q.val) :=
    (AddCommGroup.torsion _).sub_mem P.property Q.property
  apply eq_zero_of_isOfFinAddOrder_of_red_eq_zero primeFive
    (E := rationalCurve W₀) (W₀ := W₀) rfl (p := 5) (by norm_num)
    five_mem_prime five_unramified htor
  have hzero : reduceFive W₀ (P.val - Q.val) = 0 := by rw [map_sub, hPQ, sub_self]
  apply Point.map_injective (W' := W₀.toAffine) residueFiveEquiv.toIntAlgEquiv.toAlgHom
  change reduceFive W₀ (P.val - Q.val) = _
  convert hzero using 1
  rfl

/-- The genuine torsion subgroup is finite, because reduction embeds it
in the actual finite group of points over the five-element field. -/
theorem torsion_finite : Finite (AddCommGroup.torsion (rationalCurve W₀).Point) :=
  Finite.of_injective _ (reduceFive_torsion_injective W₀)

/-- A cardinality bound for the actual rational torsion subgroup. -/
theorem torsion_card_le_finite :
    Nat.card (AddCommGroup.torsion (rationalCurve W₀).Point) ≤
      Nat.card (finiteCurve W₀).Point :=
  Nat.card_le_card_of_injective _ (reduceFive_torsion_injective W₀)

#print axioms reduceFive_torsion_injective
#print axioms torsion_card_le_finite
end FourCorner.SmallReduction
