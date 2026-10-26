import CriticalFiberBounds

noncomputable section
namespace FourCorner.CriticalBadCover
open AlgebraicCurve AlgebraicCurve.RationalFunctionField CriticalBranchPlaces
variable {k : Type*} [Field k]
local instance : DecidableEq k:=Classical.decEq _
local instance : DecidableEq (RatFunc k):=Classical.decEq _
local instance : DecidableEq (Place k (RatFunc k)):=Classical.decEq _
attribute [local instance] Classical.propDecidable

abbrev extension (i : k):=CriticalRadicalField.field k i

def simple : Finset (Place k (RatFunc k)) :=
  Finset.univ.image (fun a : Fin 4=>![placeInfty k,placeOfPoint k 0,placeOfPoint k 1,placeOfPoint k (-1)] a)

lemma simple_card : (simple (k:=k)).card≤4 := by
  exact Finset.card_image_le.trans_eq (by simp)
lemma infty_mem_simple : placeInfty k∈simple (k:=k) := Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
lemma zero_mem_simple : placeOfPoint k 0∈simple (k:=k) := Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
lemma one_mem_simple : placeOfPoint k 1∈simple (k:=k) := Finset.mem_image.mpr ⟨2,Finset.mem_univ _,rfl⟩
lemma negone_mem_simple : placeOfPoint k (-1)∈simple (k:=k) := Finset.mem_image.mpr ⟨3,Finset.mem_univ _,rfl⟩

theorem branch_card_le (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) : (branch i).card≤4 := by
  have hc : (CriticalBranchPlaces.product i).roots.card≤4 := by
    have h:=Polynomial.card_roots (product_ne_zero i hi h2)
    rw [Polynomial.degree_eq_natDegree (product_ne_zero i hi h2),product_degree i hi h2] at h
    exact_mod_cast h
  exact Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans hc)

theorem branch_e_two (i : k) (hi : i^2= -1) (h2 : (2:k)≠0)
    (v : Place k (RatFunc k)) (hv : v∈branch i) (w : Place k (extension i))
    (hw : w.restrict (RatFunc k)=v) : w.ramificationIndex (RatFunc k)=2 := by
  obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hv
  rw [CriticalActualRamification.parity_index i hi h2,hw,ord_finite i hi h2 0,ord_finite i hi h2 1]
  rcases (mem_roots i hi h2 z).mp hz with hb|hc
  · simp [hb]
  · simp [hc]

def cover (i : k) (h2 : (2:k)≠0) : Finset (Place k (extension i)) := by
  classical
  letI := CriticalActualRamification.separable i h2
  exact (simple (k:=k)).biUnion (fun v=>v.fiberOver (extension i)) ∪
    (branch i).biUnion (fun v=>v.fiberOver (extension i))

theorem cover_card (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) : (cover i h2).card≤24 := by
  classical
  letI := CriticalActualRamification.separable i h2
  have hdeg:=CriticalRadicalField.degree_four k i hi h2
  have hs : ((simple (k:=k)).biUnion (fun v=>v.fiberOver (extension i))).card≤16 := by
    apply Finset.card_biUnion_le.trans
    calc
      ∑ v∈(simple (k:=k)),(v.fiberOver (extension i)).card≤∑ _v∈(simple (k:=k)),4 := by
        apply Finset.sum_le_sum
        intro v _
        simpa only [hdeg] using (CriticalFiberBounds.card_le_finrank (E:=extension i) v)
      _≤16 := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id];have h:=simple_card (k:=k);omega
  have hb : ((branch i).biUnion (fun v=>v.fiberOver (extension i))).card≤8 := by
    apply Finset.card_biUnion_le.trans
    calc
      ∑ v∈branch i,(v.fiberOver (extension i)).card≤∑ _v∈branch i,2 := by
        apply Finset.sum_le_sum
        intro v hv
        apply CriticalFiberBounds.card_le_two hdeg v
        intro w hw
        rw [branch_e_two i hi h2 v hv w (v.restrict_eq_of_mem_fiberOver hw)]
      _≤8 := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id];have h:=branch_card_le i hi h2;omega
  exact (Finset.card_union_le _ _).trans (by omega)
end FourCorner.CriticalBadCover
#print axioms FourCorner.CriticalBadCover.branch_e_two
#print axioms FourCorner.CriticalBadCover.cover_card
