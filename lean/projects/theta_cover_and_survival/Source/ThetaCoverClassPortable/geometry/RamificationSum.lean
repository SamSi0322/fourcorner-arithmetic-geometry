import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_IsCurveOver
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic

/-!
# Summing ramification over actual place fibers

This file is a conditional bridge from the actual degree and ramification
indices of a field extension to its ramification sum. The branch set is a
finite set of genuine places of the base field; its fibers are the accepted
`Place.fiberOver`, not an independently supplied combinatorial cover.
-/

noncomputable section

namespace FourCorner.RamificationSum

open AlgebraicCurve

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- Fibers over distinct base places are disjoint. -/
theorem fibers_pairwiseDisjoint (B : Finset (Place K F)) :
    (B : Set (Place K F)).PairwiseDisjoint (fun v => v.fiberOver E) := by
  intro v hv u hu hne
  apply Finset.disjoint_left.mpr
  intro w hwv hwu
  exact hne ((v.restrict_eq_of_mem_fiberOver hwv).symm.trans
    (u.restrict_eq_of_mem_fiberOver hwu))

/-- In a degree-eight extension, a fiber with index two and residue degree one
has four actual places. This is a consequence of the fundamental identity. -/
theorem card_fiberOver_eq_four
    (hdegree : Module.finrank F E = 8) (v : Place K F)
    (he : ∀ w ∈ v.fiberOver E, w.ramificationIndex F = 2)
    (hf : ∀ w ∈ v.fiberOver E, w.inertiaDeg F = 1) :
    (v.fiberOver E).card = 4 := by
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

/-- An index-two branch locus of six places contributes twenty-four to the
actual finite-support ramification sum, provided the actual residue degrees
are one. -/
theorem finsum_ramificationIndex_sub_one_eq_twentyFour_of_inertiaDeg
    (B : Finset (Place K F)) (hB : B.card = 6)
    (hdegree : Module.finrank F E = 8)
    (he : ∀ w : Place K E, w.ramificationIndex F = if w.restrict F ∈ B then 2 else 1)
    (hf : ∀ w : Place K E, w.inertiaDeg F = 1) :
    (∑ᶠ w : Place K E, ((w.ramificationIndex F : ℤ) - 1)) = 24 := by
  classical
  let S := B.biUnion (fun v => v.fiberOver E)
  have hmem (w : Place K E) : w ∈ S ↔ w.restrict F ∈ B := by
    simp only [S, Finset.mem_biUnion, Place.mem_fiberOver]
    constructor
    · rintro ⟨v, hv, hw⟩
      exact hw.symm ▸ hv
    · intro hw
      exact ⟨w.restrict F, hw, rfl⟩
  have hcard (v : Place K F) (hv : v ∈ B) : (v.fiberOver E).card = 4 := by
    apply card_fiberOver_eq_four hdegree v
    · intro w hw
      rw [he w, v.restrict_eq_of_mem_fiberOver hw, if_pos hv]
    · intro w _
      exact hf w
  have hScard : S.card = 24 := by
    dsimp [S]
    rw [Finset.card_biUnion (fibers_pairwiseDisjoint B)]
    calc
      ∑ v ∈ B, (v.fiberOver E).card = ∑ _v ∈ B, 4 :=
        Finset.sum_congr rfl hcard
      _ = 24 := by simp [hB]
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
    _ = 24 := by simp [hScard]

omit [FiniteDimensional F E] [DecidableEq (Place K F)] in
/-- Over an algebraically closed constant field, actual residue degrees are one. -/
theorem inertiaDeg_eq_one [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K E]
    (w : Place K E) : w.inertiaDeg F = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed (w.restrict F),
    IsCurveOver.deg_eq_one_of_isAlgClosed w, one_mul] at h
  exact h

/-- Six actual branch places, all of index two in a degree-eight extension,
have actual ramification sum twenty-four. -/
theorem finsum_ramificationIndex_sub_one_eq_twentyFour
    [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K E]
    (B : Finset (Place K F)) (hB : B.card = 6)
    (hdegree : Module.finrank F E = 8)
    (he : ∀ w : Place K E, w.ramificationIndex F = if w.restrict F ∈ B then 2 else 1) :
    (∑ᶠ w : Place K E, ((w.ramificationIndex F : ℤ) - 1)) = 24 :=
  finsum_ramificationIndex_sub_one_eq_twentyFour_of_inertiaDeg B hB hdegree he
    inertiaDeg_eq_one

/-- Conditional Riemann–Hurwitz bridge for actual function fields. The actual
field degree and the ramification-index formula remain explicit hypotheses;
this theorem does not assert those geometric inputs for a particular cover. -/
theorem genusFF_eq_five_of_degree_eight_and_six_branch_places
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [IsCurveOver K E]
    (hF : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hgenus : genusFF K F = 0)
    (B : Finset (Place K F)) (hB : B.card = 6)
    (hdegree : Module.finrank F E = 8)
    (he : ∀ w : Place K E, w.ramificationIndex F = if w.restrict F ∈ B then 2 else 1) :
    genusFF K E = 5 := by
  have htame : ∀ w : Place K E, ((w.ramificationIndex F : ℕ) : K) ≠ 0 := by
    intro w
    exact_mod_cast (Nat.ne_of_gt (w.ramificationIndex_pos (F := F)))
  have hrh := two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame hF htame
  have hsum := finsum_ramificationIndex_sub_one_eq_twentyFour B hB hdegree he
  rw [hdegree, hgenus, hsum] at hrh
  omega

end FourCorner.RamificationSum

#print axioms FourCorner.RamificationSum.fibers_pairwiseDisjoint
#print axioms FourCorner.RamificationSum.card_fiberOver_eq_four
#print axioms FourCorner.RamificationSum.finsum_ramificationIndex_sub_one_eq_twentyFour_of_inertiaDeg

#print axioms FourCorner.RamificationSum.inertiaDeg_eq_one
#print axioms FourCorner.RamificationSum.finsum_ramificationIndex_sub_one_eq_twentyFour

#print axioms FourCorner.RamificationSum.genusFF_eq_five_of_degree_eight_and_six_branch_places
