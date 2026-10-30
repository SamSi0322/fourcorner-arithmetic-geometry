import CriticalBadUnits
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one

noncomputable section
namespace FourCorner.CriticalBadPlaces
open AlgebraicCurve AlgebraicCurve.RationalFunctionField
open CriticalRadicalField CriticalBadCover CriticalBadUnits
variable {k : Type*} [Field k]
local instance : DecidableEq (RatFunc k):=Classical.decEq _
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

/-- Actual degree-one places failing the original ordered four-unit condition. -/
def bad (i : k) : Set (Place k (field k i)) := {w | w.deg=1 ∧ ¬good i w}

lemma mem_cover_of_restrict (i : k) (h2 : (2:k)≠0) (w : Place k (field k i))
    (hv : w.restrict (RatFunc k)∈simple (k:=k) ∨ w.restrict (RatFunc k)∈CriticalBranchPlaces.branch i) :
    w∈cover i h2 := by
  classical
  letI := CriticalActualRamification.separable i h2
  change w∈(simple (k:=k)).biUnion (fun v=>v.fiberOver (field k i)) ∪
    (CriticalBranchPlaces.branch i).biUnion (fun v=>v.fiberOver (field k i))
  simp only [Finset.mem_union,Finset.mem_biUnion,Place.mem_fiberOver]
  rcases hv with hv|hv
  · exact Or.inl ⟨w.restrict (RatFunc k),hv,rfl⟩
  · exact Or.inr ⟨w.restrict (RatFunc k),hv,rfl⟩

/-- No replacement place: the same actual rational bad place is contained in
an explicitly bounded native base-place fiber, with infinity included. -/
theorem rational_bad_mem_cover (i : k) (hi : i^2= -1) (h2 : (2:k)≠0)
    (w : Place k (field k i)) (hw : w.IsRational) (hbad : ¬good i w) : w∈cover i h2 := by
  letI : NeZero (2:k):=⟨h2⟩
  apply mem_cover_of_restrict i h2 w
  by_cases ha : a k i∈w.toValuationSubring
  · let z:=ResiduePlaceEvaluation.evaluate w hw ⟨a k i,ha⟩
    have hv : w.restrict (RatFunc k)=placeOfPoint k z :=
      RationalLinePlaceImage.finite_image w hw ha
    by_cases h0 : z=0
    · left;rw [hv,h0];exact zero_mem_simple
    by_cases h1 : z=1
    · left;rw [hv,h1];exact one_mem_simple
    by_cases hm : z= -1
    · left;rw [hv,hm];exact negone_mem_simple
    by_cases hr : placeOfPoint k z∈CriticalBranchPlaces.branch i
    · right;rw [hv];exact hr
    have hbc:=not_or.mp ((CriticalBranchPlaces.finite_mem_branch i hi h2 z).not.mp hr)
    exact (hbad (finite_good i w z hv h0 h1 hm hbc.1 hbc.2)).elim
  · left
    rw [RationalLinePlaceImage.infinity_image w ha]
    exact infty_mem_simple

theorem bad_subset_cover (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) : bad i⊆(cover i h2 : Set _) := by
  rintro w ⟨hw,hbad⟩
  exact rational_bad_mem_cover i hi h2 w (w.isRational_iff_deg_eq_one.mpr hw) hbad

/-- Complete actual bad-place bound. It is valid over ANY field, hence in
particular finite and perfect fields, with no genus/Hasse/point-count premise. -/
theorem finite_and_card_le_twentyFour (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    (bad i).Finite ∧ Nat.card (bad i)≤24 := by
  have hs:=bad_subset_cover i hi h2
  refine ⟨(cover i h2).finite_toSet.subset hs,?_⟩
  change (bad i).ncard≤24
  have h:=Set.ncard_le_ncard hs (cover i h2).finite_toSet
  rw [Set.ncard_coe_finset] at h
  exact h.trans (cover_card i hi h2)

/-- Explicit spelling of the exact literal functions in the bounded set,
with all four nonzero global elements proved in the same result. -/
theorem actual_bad_places (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    a k i≠0 ∧ b k i≠0 ∧ c k i≠0 ∧ a k i^2-1≠0 ∧
    {w : Place k (field k i) | w.deg=1 ∧
      ¬(w.ord (a k i)=0 ∧ w.ord (b k i)=0 ∧ w.ord (c k i)=0 ∧ w.ord (a k i^2-1)=0)}.Finite ∧
    Nat.card {w : Place k (field k i) | w.deg=1 ∧
      ¬(w.ord (a k i)=0 ∧ w.ord (b k i)=0 ∧ w.ord (c k i)=0 ∧ w.ord (a k i^2-1)=0)}≤24 := by
  have hn:=ordered_nonzero i hi h2
  have hb:=finite_and_card_le_twentyFour i hi h2
  exact ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,hb.1,hb.2⟩
end FourCorner.CriticalBadPlaces
#print axioms FourCorner.CriticalBadPlaces.rational_bad_mem_cover
#print axioms FourCorner.CriticalBadPlaces.finite_and_card_le_twentyFour
#print axioms FourCorner.CriticalBadPlaces.actual_bad_places
