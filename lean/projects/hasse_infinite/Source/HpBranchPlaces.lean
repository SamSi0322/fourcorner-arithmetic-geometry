import HpFieldGeometry
import OddFourPlaces

namespace FourCorner.HpBranchPlaces

open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField HpLiteralField
noncomputable section
variable (K : Type*) [Field K] [NeZero (2 : K)]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (RatFunc K) := Classical.decEq _

def coefficient (p : K) : Fin 4 → K
  | 0 => p
  | 1 => 2*(p-1)
  | 2 => 2*(p+1)
  | 3 => p-1

theorem coefficient_ne_zero (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 4) :
    coefficient K p i ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne _
  fin_cases i
  · exact hp
  · exact mul_ne_zero h2 ha
  · exact mul_ne_zero h2 hb
  · exact ha

theorem poly_factor (p : K) (ha : p-1 ≠ 0) (i : Fin 4) :
    poly K p i=C (coefficient K p i)*(X-C (branch K p i)) := by
  fin_cases i
  · simp [poly,coefficient,branch]
  · simp [poly,coefficient,branch]
  · simp [poly,coefficient,branch]
  · change C (p-1)*X+C (p+1)=C (p-1)*(X-C (-(p+1)/(p-1)))
    have he : C (p-1)*C (-(p+1)/(p-1))= -C (p+1) := by
      rw [← C_mul,← C_neg]
      congr 1
      field_simp
    rw [mul_sub,he]
    ring

theorem radicand_factor (p : K) (ha : p-1 ≠ 0) (i : Fin 4) :
    radicand K p i=algebraMap K (RatFunc K) (coefficient K p i)*OddFourPlaces.linear (branch K p i) := by
  rw [radicand,poly_factor K p ha i,map_mul,RatFunc.algebraMap_C]
  rfl

theorem ord_finite (p z : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 4) :
    (placeOfPoint K z).ord (radicand K p i)=if z=branch K p i then 1 else 0 := by
  classical
  have hc := (map_ne_zero (algebraMap K (RatFunc K))).mpr (coefficient_ne_zero K p hp ha hb i)
  rw [radicand_factor K p ha i,(placeOfPoint K z).ord_mul hc (OddFourPlaces.linear_ne_zero _),
    Place.ord_algebraMap,zero_add,OddFourPlaces.ord_linear_finite]

theorem ord_infty (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 4) :
    (placeInfty K).ord (radicand K p i)= -1 := by
  classical
  have hc := (map_ne_zero (algebraMap K (RatFunc K))).mpr (coefficient_ne_zero K p hp ha hb i)
  rw [radicand_factor K p ha i,(placeInfty K).ord_mul hc (OddFourPlaces.linear_ne_zero _),
    Place.ord_algebraMap,zero_add,OddFourPlaces.ord_linear_infty]

theorem branch_injective (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    Function.Injective (branch K p) := by
  intro i j h
  by_contra hij
  have hn := poly_eval_other K p hp ha hb i j (Ne.symm hij)
  rw [h,poly_eval_self K p ha j] at hn
  exact hn rfl

theorem ord_private (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i j : Fin 4) :
    (placeOfPoint K (branch K p i)).ord (radicand K p j)=if i=j then 1 else 0 := by
  rw [ord_finite K p _ hp ha hb j]
  simp only [(branch_injective K p hp ha hb).eq_iff]

def finiteBranches (p : K) : Finset (Place K (RatFunc K)) := by
  classical
  exact Finset.univ.image (fun i : Fin 4 => placeOfPoint K (branch K p i))

def support (p : K) : Finset (Place K (RatFunc K)) := by
  classical
  exact insert (placeInfty K) (finiteBranches K p)

theorem mem_finiteBranches (p : K) (v : Place K (RatFunc K)) :
    v∈finiteBranches K p ↔ ∃i,placeOfPoint K (branch K p i)=v := by
  classical
  simp [finiteBranches]

theorem infinity_not_finiteBranches (p : K) : placeInfty K∉finiteBranches K p := by
  intro h
  obtain ⟨i,hi⟩ := (mem_finiteBranches K p _).mp h
  exact placeOfPoint_ne_placeInfty K _ hi

theorem support_card (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) : (support K p).card=5 := by
  classical
  have hinj : Function.Injective (fun i : Fin 4 => placeOfPoint K (branch K p i)) :=
    (placeOfPoint_injective K).comp (branch_injective K p hp ha hb)
  rw [support,Finset.card_insert_of_notMem (infinity_not_finiteBranches K p),finiteBranches,
    Finset.card_image_of_injective _ hinj]
  decide

theorem ord_off (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (v : Place K (RatFunc K)) (hv : v∉support K p) (i : Fin 4) : v.ord (radicand K p i)=0 := by
  classical
  have hv' : v ≠ placeInfty K ∧ v∉finiteBranches K p := by simpa only [support,Finset.mem_insert,not_or] using hv
  have hi : v ≠ placeOfPoint K (branch K p i) := by
    intro he
    exact hv'.2 ((mem_finiteBranches K p v).mpr ⟨i,he.symm⟩)
  have hc := (map_ne_zero (algebraMap K (RatFunc K))).mpr (coefficient_ne_zero K p hp ha hb i)
  rw [radicand_factor K p ha i,v.ord_mul hc (OddFourPlaces.linear_ne_zero _),
    Place.ord_algebraMap,zero_add,OddFourPlaces.ord_linear_off v _ hv'.1 hi]

theorem exists_odd_iff_mem_support (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (v : Place K (RatFunc K)) : (∃i,Odd (v.ord (radicand K p i))) ↔ v∈support K p := by
  classical
  constructor
  · rintro ⟨i,hi⟩
    by_contra hn
    rw [ord_off K p hp ha hb v hn i] at hi
    norm_num at hi
  · intro h
    simp only [support,Finset.mem_insert] at h
    rcases h with rfl | h
    · refine ⟨0,?_⟩
      rw [ord_infty K p hp ha hb]
      norm_num
    · obtain ⟨i,rfl⟩ := (mem_finiteBranches K p v).mp h
      refine ⟨i,?_⟩
      rw [ord_private K p hp ha hb i i]
      simp

#print axioms support_card
#print axioms exists_odd_iff_mem_support
#print axioms ord_off

end
end FourCorner.HpBranchPlaces
