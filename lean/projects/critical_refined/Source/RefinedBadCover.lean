import RefinedFiniteSource
import RefinedCoverHasse
import CriticalFiberBounds
import CriticalBadPlaces

noncomputable section
namespace FourCorner.RefinedBadCover
open AlgebraicCurve CriticalRadicalField CriticalBadUnits CriticalBadPlaces
open CriticalBoundaryClassification CriticalBoundaryEight
variable {k:Type*} [Field k]
set_option maxHeartbeats 2000000
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (field k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (field k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (field k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

def badCover (i:k) (hi:i^2= -1) (h2:(2:k)≠0) : Finset (Place k (CriticalLiteralDouble.field k i)) := by
  classical
  letI := CriticalLiteralDouble.separable k i h2
  exact (finite_and_card_le_twentyFour i hi h2).1.toFinset.biUnion
    (fun v=>v.fiberOver (CriticalLiteralDouble.field k i))

/-- Every actual rational cover place whose original restriction is bad is
contained in this genuine finite union of actual place fibres. -/
theorem mem_badCover (i:k) (hi:i^2= -1) (h2:(2:k)≠0)
    (w:Place k (CriticalLiteralDouble.field k i)) (hw:w.IsRational)
    (hg:¬good i (w.restrict (field k i))) : w∈badCover i hi h2 := by
  classical
  letI := CriticalLiteralDouble.separable k i h2
  have hv := CriticalRationalFibres.restrict_rational (F:=field k i) w hw
  change w∈(finite_and_card_le_twentyFour i hi h2).1.toFinset.biUnion _
  apply Finset.mem_biUnion.mpr
  refine ⟨w.restrict (field k i),?_,Place.restrict_mem_fiberOver w⟩
  exact (Set.Finite.mem_toFinset (finite_and_card_le_twentyFour i hi h2).1).mpr ⟨(w.restrict (field k i)).isRational_iff_deg_eq_one.mp hv,hg⟩

/-- Degree two bounds all actual fibres, even their nonrational places. -/
theorem badCover_card (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    (badCover i hi h2).card≤2*Nat.card (bad i) := by
  classical
  letI := CriticalLiteralDouble.separable k i h2
  let S := (finite_and_card_le_twentyFour i hi h2).1.toFinset
  have hS:S.card=Nat.card (bad i) := by
    change S.card=(bad i).ncard
    exact (Set.ncard_eq_toFinset_card (bad i) (finite_and_card_le_twentyFour i hi h2).1).symm
  change (S.biUnion (fun v=>v.fiberOver (CriticalLiteralDouble.field k i))).card≤_
  calc
    _≤∑ v∈S,(v.fiberOver (CriticalLiteralDouble.field k i)).card := Finset.card_biUnion_le
    _≤∑ _v∈S,2 := by
      apply Finset.sum_le_sum
      intro v hv
      have h:=CriticalFiberBounds.card_le_finrank (E:=CriticalLiteralDouble.field k i) v
      rwa [CriticalDoublePointCount.degree_two k i hi h2] at h
    _=2*Nat.card (bad i) := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,hS];omega

theorem badCover_le_fortyEight (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    (badCover i hi h2).card≤48 := by
  have h:=badCover_card i hi h2
  have hb:Nat.card (bad i)≤24 := (finite_and_card_le_twentyFour i hi h2).2
  omega

/-- A true cover-place count strictly exceeding the actual bad union leaves
one rational place with all four original unit conditions. -/
theorem exists_good_cover_of_card (i:k) (hi:i^2= -1) (h2:(2:k)≠0)
    (hN:(badCover i hi h2).card<Nat.card {w:Place k (CriticalLiteralDouble.field k i) //w.deg=1}) :
    ∃w:Place k (CriticalLiteralDouble.field k i), w.IsRational ∧ good i (w.restrict (field k i)) := by
  classical
  by_contra! hn
  have hsub:{w:Place k (CriticalLiteralDouble.field k i) | w.deg=1 } ⊆(badCover i hi h2:Set _) := by
    intro w hw
    have hwr:w.IsRational := w.isRational_iff_deg_eq_one.mpr hw
    exact mem_badCover i hi h2 w hwr (hn w hwr)
  have hc:=Set.ncard_le_ncard hsub (badCover i hi h2).finite_toSet
  rw [Set.ncard_coe_finset] at hc
  change Nat.card {w:Place k (CriticalLiteralDouble.field k i) //w.deg=1}≤(badCover i hi h2).card at hc
  omega

theorem exists_good_cover_large [Finite k] (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (hq:73≤Nat.card k) :
    ∃w:Place k (CriticalLiteralDouble.field k i), w.IsRational ∧ good i (w.restrict (field k i)) := by
  apply exists_good_cover_of_card i hi h2
  have hN:=RefinedCoverHasse.count_gt_fortyEight k i hi h2 hq
  have hbad:=badCover_le_fortyEight i hi h2
  omega

/-- When the SAME original a,b,c are units at every rational base place,
the only bad rational base places are contained in the ACTUAL base-eight
boundary. This helper's arithmetic premise is discharged in the5mod8 case. -/
theorem bad_base_le_eight_of_units (i:k) (hi:i^2= -1) (h2:(2:k)≠0)
    (hunit:∀v:Place k (field k i),v.IsRational→
      v.ord (a k i)=0 ∧ v.ord (b k i)=0 ∧ v.ord (c k i)=0) : Nat.card (bad i)≤8 := by
  classical
  let f:(bad i)→Boundary i := fun v=>⟨v.val,by
    have hv:v.val.IsRational := v.val.isRational_iff_deg_eq_one.mpr v.property.1
    obtain ⟨ha,hb,hc⟩:=hunit v.val hv
    have hn: a k i^2-1≠0 := (CriticalBadUnits.ordered_nonzero i hi h2).2.2.2
    have hmem:a k i^2-1∈v.val.toValuationSubring :=
      v.val.toValuationSubring.sub_mem
        (v.val.toValuationSubring.pow_mem ((v.val.mem_iff_ord_nonneg
          (CriticalBadUnits.ordered_nonzero i hi h2).1).mpr (by rw [ha])) 2)
        v.val.toValuationSubring.one_mem
    have hs:0≤v.val.ord (a k i^2-1) := (v.val.mem_iff_ord_nonneg hn).mp hmem
    have hne:v.val.ord (a k i^2-1)≠0 := by
      intro hh
      exact v.property.2 ⟨ha,hb,hc,hh⟩
    exact ⟨hv,by change 0<v.val.ord (a k i^2-1);omega⟩⟩
  have hf:Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z:Boundary i=>z.val) hxy)
  letI:Finite (Boundary i) := Finite.of_equiv (Fin 3→Bool) (boundaryEquiv i hi h2).symm
  have h:=Nat.card_le_card_of_injective f hf
  rwa [boundary_card i hi h2] at h

theorem exists_good_cover_small_of_units [Finite k] (i:k) (hi:i^2= -1) (h2:(2:k)≠0)
    (hq:29≤Nat.card k)
    (hunit:∀v:Place k (field k i),v.IsRational→
      v.ord (a k i)=0 ∧ v.ord (b k i)=0 ∧ v.ord (c k i)=0) :
    ∃w:Place k (CriticalLiteralDouble.field k i), w.IsRational ∧ good i (w.restrict (field k i)) := by
  apply exists_good_cover_of_card i hi h2
  have hN:=RefinedCoverHasse.count_gt_sixteen k i hi h2 hq
  have hbad:=badCover_card i hi h2
  have hbase:=bad_base_le_eight_of_units i hi h2 hunit
  omega

#print axioms badCover_card
#print axioms exists_good_cover_large
#print axioms bad_base_le_eight_of_units
#print axioms exists_good_cover_small_of_units
end FourCorner.RefinedBadCover
