import HpGeometricGenus

namespace FourCorner.HpRootOrders
open AlgebraicCurve AlgebraicCurve.RationalFunctionField HpLiteralField HpBranchPlaces
noncomputable section
variable (K : Type*) [Field K] [IsAlgClosed K] [NeZero (2 : K)]
attribute [local instance] Classical.propDecidable

 theorem root_ne_zero (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 4) :
    root K p i ≠ 0 := by
  intro hz
  have hrad : radicand K p i ≠ 0 := by
    rw [radicand_factor K p ha]
    exact mul_ne_zero ((map_ne_zero _).mpr (coefficient_ne_zero K p hp ha hb i))
      (OddFourPlaces.linear_ne_zero _)
  have hh := root_sq K p i
  rw [hz,zero_pow (by decide : 2 ≠ 0)] at hh
  exact ((map_ne_zero (algebraMap (RatFunc K) (field K p))).mpr hrad) hh.symm

 theorem twice_order (p : K) (w : Place K (field K p)) (i : Fin 4) :
    2*w.ord (root K p i)=(w.ramificationIndex (RatFunc K) : ℤ)*
      (w.restrict (RatFunc K)).ord (radicand K p i) := by
  letI := finite_over_line K p
  have hh := congrArg w.ord (root_sq K p i)
  rw [show root K p i^2=root K p i^(2 : ℤ) from (zpow_ofNat _ _).symm,
    w.ord_zpow,w.ord_restrict] at hh
  exact hh

 theorem at_infinity (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (w : Place K (field K p)) (hw : w.restrict (RatFunc K)=placeInfty K) (i : Fin 4) :
    w.ord (root K p i)= -1 := by
  have hh := twice_order K p w i
  have hi : w.ramificationIndex (RatFunc K)=2 := by
    rw [HpGeometricGenus.actual_index_formula K p hp ha hb,hw]
    exact if_pos (Finset.mem_insert_self _ _)
  rw [hi,hw,ord_infty K p hp ha hb] at hh
  norm_num at hh
  omega

 theorem at_branch (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (w : Place K (field K p)) (j : Fin 4)
    (hw : w.restrict (RatFunc K)=placeOfPoint K (branch K p j)) (i : Fin 4) :
    w.ord (root K p i)=if j=i then 1 else 0 := by
  have hh := twice_order K p w i
  have hm : placeOfPoint K (branch K p j)∈support K p := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have hi : w.ramificationIndex (RatFunc K)=2 := by
    rw [HpGeometricGenus.actual_index_formula K p hp ha hb,hw]
    exact if_pos hm
  rw [hi,hw,ord_private K p hp ha hb] at hh
  split_ifs at hh ⊢ <;> omega

 theorem off_support (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (w : Place K (field K p)) (hw : w.restrict (RatFunc K)∉support K p) (i : Fin 4) :
    w.ord (root K p i)=0 := by
  have hh := twice_order K p w i
  have hne : w.restrict (RatFunc K) ≠ placeInfty K := by
    intro h;exact hw (h ▸ Finset.mem_insert_self _ _)
  have hi : w.ramificationIndex (RatFunc K)=1 := by
    rw [HpGeometricGenus.actual_index_formula K p hp ha hb,if_neg hw]
  have hv (j : Fin 4) : w.restrict (RatFunc K) ≠ placeOfPoint K (branch K p j) := by
    intro h
    apply hw
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  rw [hi,ord_off K p hp ha hb _ hw i] at hh
  omega

#print axioms root_ne_zero
#print axioms twice_order
#print axioms at_infinity
#print axioms at_branch
#print axioms off_support
end
end FourCorner.HpRootOrders
