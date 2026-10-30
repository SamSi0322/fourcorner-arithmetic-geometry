import ThetaCoverClassPortable.geometry.RamificationSum
import ThetaCoverClassPortable.geometry.RatFuncFiniteExtension

/-!
# Degree-four ramification and the genus-five consequence

This conditional bridge concerns an actual finite extension of `K(X)`.
Its hypotheses are the actual field degree four and the actual index-two
ramification pattern above eight genuine base places. Residue degrees,
fiber sizes, the ramification sum, and the base genus are derived.
The theorem does not supply the degree or ramification pattern of a
particular model.
-/

noncomputable section

namespace FourCorner.BiquadraticRamificationSum

open AlgebraicCurve

section GeneralBase

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- The fundamental identity forces two actual places in an index-two fiber
of a degree-four extension when residue degrees are one. -/
theorem card_fiberOver_eq_two
    (hdegree : Module.finrank F E = 4) (v : Place K F)
    (he : ∀ w ∈ v.fiberOver E, w.ramificationIndex F = 2)
    (hf : ∀ w ∈ v.fiberOver E, w.inertiaDeg F = 1) :
    (v.fiberOver E).card = 2 := by
  have hsum := v.sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := E)
  have hconst :
      (∑ w ∈ v.fiberOver E, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) =
        (v.fiberOver E).card * (2 : ℤ) := by
    calc
      _ = ∑ _w ∈ v.fiberOver E, (2 : ℤ) := by
        apply Finset.sum_congr rfl
        intro w hw
        simp only [he w hw, hf w hw, Nat.cast_ofNat, Nat.cast_one, mul_one]
      _ = _ := by simp
  rw [hconst, hdegree] at hsum
  omega

variable [DecidableEq (Place K F)]

/-- Eight genuine branch places give a ramification sum of sixteen; the
summation is over the actual place fibers and their disjoint union. -/
theorem finsum_ramificationIndex_sub_one_eq_sixteen
    [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K E]
    (B : Finset (Place K F)) (hB : B.card = 8)
    (hdegree : Module.finrank F E = 4)
    (he : ∀ w : Place K E, w.ramificationIndex F = if w.restrict F ∈ B then 2 else 1) :
    (∑ᶠ w : Place K E, ((w.ramificationIndex F : ℤ) - 1)) = 16 := by
  classical
  let S := B.biUnion (fun v => v.fiberOver E)
  have hmem (w : Place K E) : w ∈ S ↔ w.restrict F ∈ B := by
    simp only [S, Finset.mem_biUnion, Place.mem_fiberOver]
    constructor
    · rintro ⟨v, hv, hw⟩
      exact hw.symm ▸ hv
    · intro hw
      exact ⟨w.restrict F, hw, rfl⟩
  have hcard (v : Place K F) (hv : v ∈ B) : (v.fiberOver E).card = 2 := by
    apply card_fiberOver_eq_two hdegree v
    · intro w hw
      rw [he w, v.restrict_eq_of_mem_fiberOver hw, if_pos hv]
    · intro w _
      exact RamificationSum.inertiaDeg_eq_one w
  have hScard : S.card = 16 := by
    dsimp [S]
    rw [Finset.card_biUnion (RamificationSum.fibers_pairwiseDisjoint B)]
    calc
      ∑ v ∈ B, (v.fiberOver E).card = ∑ _v ∈ B, 2 :=
        Finset.sum_congr rfl hcard
      _ = 16 := by simp [hB]
  have hsupp : Function.support (fun w : Place K E => (w.ramificationIndex F : ℤ) - 1) ⊆ S := by
    intro w hw
    apply (hmem w).mpr
    by_contra hnot
    have hew : w.ramificationIndex F = 1 := by rw [he w, if_neg hnot]
    exact hw (by simp [hew])
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  calc
    ∑ w ∈ S, ((w.ramificationIndex F : ℤ) - 1) = ∑ _w ∈ S, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [he w, if_pos ((hmem w).mp hw)]
      norm_num
    _ = 16 := by simp [hScard]

end GeneralBase

section RationalBase

variable {K E : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Field E]
  [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
  [FiniteDimensional (RatFunc K) E] [DecidableEq (Place K (RatFunc K))]

/-- The actual branch fibers contain two places. Curve structures and residue
degrees are derived from the finite extension of the rational function field. -/
theorem card_branch_fiberOver_eq_two
    (B : Finset (Place K (RatFunc K)))
    (hdegree : Module.finrank (RatFunc K) E = 4)
    (he : ∀ w : Place K E,
      w.ramificationIndex (RatFunc K) = if w.restrict (RatFunc K) ∈ B then 2 else 1)
    (v : Place K (RatFunc K)) (hv : v ∈ B) :
    (v.fiberOver E).card = 2 := by
  let : IsCurveOver K (RatFunc K) :=
    RatFuncFiniteExtension.isCurveOver_of_charZero K (RatFunc K)
  let : IsCurveOver K E := RatFuncFiniteExtension.isCurveOver_of_charZero K E
  apply card_fiberOver_eq_two hdegree v
  · intro w hw
    rw [he w, v.restrict_eq_of_mem_fiberOver hw, if_pos hv]
  · intro w _
    exact RamificationSum.inertiaDeg_eq_one w

/-- The genuine ramification sum for a degree-four extension of `K(X)` with
eight index-two branch places is sixteen. No curve structure is assumed. -/
theorem ratFunc_finsum_ramificationIndex_sub_one_eq_sixteen
    (B : Finset (Place K (RatFunc K))) (hB : B.card = 8)
    (hdegree : Module.finrank (RatFunc K) E = 4)
    (he : ∀ w : Place K E,
      w.ramificationIndex (RatFunc K) = if w.restrict (RatFunc K) ∈ B then 2 else 1) :
    (∑ᶠ w : Place K E, ((w.ramificationIndex (RatFunc K) : ℤ) - 1)) = 16 := by
  let : IsCurveOver K (RatFunc K) :=
    RatFuncFiniteExtension.isCurveOver_of_charZero K (RatFunc K)
  let : IsCurveOver K E := RatFuncFiniteExtension.isCurveOver_of_charZero K E
  exact finsum_ramificationIndex_sub_one_eq_sixteen B hB hdegree he

/-- Conditional genus-five assembly for actual degree-four function fields.
The accepted Riemann--Hurwitz theorem uses the derived ramification sum and
the proved genus-zero rational base. The degree and place-index formula are
explicit geometric inputs that must be established for the intended model. -/
theorem genusFF_eq_five_of_degree_four_and_eight_branch_places
    (B : Finset (Place K (RatFunc K))) (hB : B.card = 8)
    (hdegree : Module.finrank (RatFunc K) E = 4)
    (he : ∀ w : Place K E,
      w.ramificationIndex (RatFunc K) = if w.restrict (RatFunc K) ∈ B then 2 else 1) :
    genusFF K E = 5 := by
  have htame : ∀ w : Place K E, ((w.ramificationIndex (RatFunc K) : ℕ) : K) ≠ 0 := by
    intro w
    exact_mod_cast (Nat.ne_of_gt (w.ramificationIndex_pos (F := RatFunc K)))
  have hrh := two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
    (RatFuncFiniteExtension.base_oneVariable K) htame
  have hsum := ratFunc_finsum_ramificationIndex_sub_one_eq_sixteen B hB hdegree he
  rw [hdegree, RatFuncFiniteExtension.genus_base_eq_zero K, hsum] at hrh
  omega

end RationalBase

end FourCorner.BiquadraticRamificationSum

#print axioms FourCorner.BiquadraticRamificationSum.card_fiberOver_eq_two
#print axioms FourCorner.BiquadraticRamificationSum.finsum_ramificationIndex_sub_one_eq_sixteen
#print axioms FourCorner.BiquadraticRamificationSum.card_branch_fiberOver_eq_two
#print axioms FourCorner.BiquadraticRamificationSum.ratFunc_finsum_ramificationIndex_sub_one_eq_sixteen
#print axioms FourCorner.BiquadraticRamificationSum.genusFF_eq_five_of_degree_four_and_eight_branch_places
