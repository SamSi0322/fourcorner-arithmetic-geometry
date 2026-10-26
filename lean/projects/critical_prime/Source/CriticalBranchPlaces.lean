import CriticalTwoRamification
import geometry.OppositePlaceOrders

noncomputable section
namespace FourCorner.CriticalBranchPlaces
open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField
variable {K : Type*} [Field K]
local instance : DecidableEq K:=Classical.decEq K
local instance : DecidableEq (RatFunc K):=Classical.decEq _

def polynomial (i : K) : Fin 2 → K[X]
  | 0=>CriticalSquareclasses.qB i
  | 1=>CriticalSquareclasses.qC i
abbrev radicand (i : K) (a : Fin 2) : RatFunc K := algebraMap K[X] (RatFunc K) (polynomial i a)

theorem polynomial_separable (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) (a : Fin 2) :
    (polynomial i a).Separable := by
  have hi0:=CriticalElliptic23.iota_nonzero i hi
  have him:=CriticalElliptic23.iota_ne_one i hi h2
  have hip:=CriticalElliptic23.iota_add_one_nonzero i hi h2
  fin_cases a
  · exact CriticalSquareclasses.quadratic_separable hi0 (sub_ne_zero.mpr (Ne.symm him)) h2
  · exact CriticalSquareclasses.quadratic_separable hip (neg_ne_zero.mpr hi0) h2

theorem polynomial_degree (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) (a : Fin 2) :
    (polynomial i a).natDegree=2 := by
  have hi0:=CriticalElliptic23.iota_nonzero i hi
  have hip:=CriticalElliptic23.iota_add_one_nonzero i hi h2
  fin_cases a
  · change (CriticalSquareclasses.qB i).natDegree=2
    rw [CriticalSquareclasses.qB,CriticalSquareclasses.quadratic,
      natDegree_add_C,natDegree_C_mul hi0,natDegree_X_pow]
  · change (CriticalSquareclasses.qC i).natDegree=2
    rw [CriticalSquareclasses.qC,CriticalSquareclasses.quadratic,
      natDegree_add_C,natDegree_C_mul hip,natDegree_X_pow]

theorem polynomial_ne_zero (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) (a : Fin 2) : polynomial i a≠0 := by
  intro hz
  have hd:=polynomial_degree i hi h2 a
  rw [hz,natDegree_zero] at hd
  omega

theorem radicand_ne_zero (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) (a : Fin 2) : radicand i a≠0 :=
  RatFunc.algebraMap_ne_zero (polynomial_ne_zero i hi h2 a)

def product (i : K) : K[X]:=polynomial i 0*polynomial i 1

theorem product_ne_zero (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) : product i≠0 :=
  mul_ne_zero (polynomial_ne_zero i hi h2 0) (polynomial_ne_zero i hi h2 1)
theorem product_separable (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) : (product i).Separable :=
  (polynomial_separable i hi h2 0).mul (polynomial_separable i hi h2 1) (CriticalSquareclasses.coprime i)
theorem product_degree (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) : (product i).natDegree=4 := by
  rw [product,natDegree_mul (polynomial_ne_zero i hi h2 0) (polynomial_ne_zero i hi h2 1),
    polynomial_degree i hi h2 0,polynomial_degree i hi h2 1]

def roots (i : K) : Finset K := (product i).roots.toFinset

theorem mem_roots (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) (z : K) :
    z∈roots i ↔ (polynomial i 0).eval z=0 ∨ (polynomial i 1).eval z=0 := by
  rw [roots,Multiset.mem_toFinset,Polynomial.mem_roots (product_ne_zero i hi h2),product]
  change (polynomial i 0*polynomial i 1).eval z=0 ↔ _
  rw [eval_mul,mul_eq_zero]

theorem roots_card [IsAlgClosed K] (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) : (roots i).card=4 := by
  rw [roots,Multiset.toFinset_card_of_nodup (nodup_roots (product_separable i hi h2)),
    IsAlgClosed.card_roots_eq_natDegree,product_degree i hi h2]

def branch (i : K) : Finset (Place K (RatFunc K)) := (roots i).image (placeOfPoint K)

theorem branch_card [IsAlgClosed K] (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) : (branch i).card=4 := by
  rw [branch,Finset.card_image_of_injective _ (placeOfPoint_injective K),roots_card i hi h2]

theorem finite_mem_branch (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) (z : K) :
    placeOfPoint K z∈branch i ↔ (polynomial i 0).eval z=0 ∨ (polynomial i 1).eval z=0 := by
  rw [branch,Finset.mem_image]
  constructor
  · rintro ⟨y,hy,he⟩
    have hyz:=placeOfPoint_injective K he
    subst y
    exact (mem_roots i hi h2 z).mp hy
  · intro h
    exact ⟨z,(mem_roots i hi h2 z).mpr h,rfl⟩

theorem infty_not_branch (i : K) : placeInfty K∉branch i := by
  rintro h
  obtain ⟨z,hz,he⟩:=Finset.mem_image.mp h
  exact placeOfPoint_ne_placeInfty K z he

theorem ord_finite (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) (a : Fin 2) (z : K) :
    (placeOfPoint K z).ord (radicand i a)=if (polynomial i a).eval z=0 then 1 else 0 := by
  by_cases hz : (polynomial i a).eval z=0
  · rw [if_pos hz,radicand,OppositePlaceOrders.ord_polynomial z (polynomial_ne_zero i hi h2 a)]
    have hm : (polynomial i a).rootMultiplicity z=1 := by
      apply Nat.le_antisymm (rootMultiplicity_le_one_of_separable (polynomial_separable i hi h2 a) z)
      exact (rootMultiplicity_pos (polynomial_ne_zero i hi h2 a)).mpr hz
    rw [hm];rfl
  · rw [if_neg hz]
    exact OppositePlaceOrders.ord_polynomial_eq_zero_of_eval_ne_zero z hz

theorem ord_infty (i : K) (hi : i^2= -1) (h2 : (2:K)≠0) (a : Fin 2) :
    (placeInfty K).ord (radicand i a)= -2 := by
  rw [radicand,OppositePlaceOrders.ord_polynomial_infty (polynomial_ne_zero i hi h2 a),polynomial_degree i hi h2 a]
  rfl
end FourCorner.CriticalBranchPlaces
#print axioms FourCorner.CriticalBranchPlaces.branch_card
#print axioms FourCorner.CriticalBranchPlaces.finite_mem_branch
#print axioms FourCorner.CriticalBranchPlaces.ord_finite
#print axioms FourCorner.CriticalBranchPlaces.ord_infty
