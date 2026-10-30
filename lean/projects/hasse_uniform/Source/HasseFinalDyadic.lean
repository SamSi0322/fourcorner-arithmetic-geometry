import HasseUnitFifteenRow
import HasseDyadicUnitOneRow
import HasseFiniteAssembly

namespace FourCorner.HasseFinalDyadic

open HasseRationalSource HasseAnchorChoice HasseTangentGlobal HasseConstantCorrection
open HasseObstructionArithmetic HasseConstantDyadic HasseSignAlgebra HasseFiniteAssembly

theorem correctedSign_unitOne (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) (h : UnitOne p) :
    correctedSign p hp P D 2=bitSign (depthIndicator (padicValRat 2 (p-1))) := by
  rw [correctedSign,HasseDyadicUnitOneRow.tangentSign_unitOne p hp hL P D h,
    constantSign_unitOne p hp hL h]
  by_cases hv : padicValRat 2 (p-1)=5
  · simp only [hv,ite_true,depthIndicator,bitSign_one]
    norm_num
  · simp only [hv,ite_false,depthIndicator,bitSign_zero]
    norm_num

theorem correctedSign_unitFifteen (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) (h : UnitFifteen p) :
    correctedSign p hp P D 2=bitSign (depthIndicator (padicValRat 2 (p+1))+A p+B p) := by
  rw [correctedSign,HasseUnitFifteenRow.tangentSign_unitFifteen p hp hL P D h,
    constantSign_unitFifteen p hp hL h,mul_one,HasseWR.global_wsupport p hp hL P D]
  have hi : (-1 : ℤ)^(if padicValRat 2 (p+1)=5 then 1 else 0)=
      bitSign (depthIndicator (padicValRat 2 (p+1))) := by
    by_cases hv : padicValRat 2 (p+1)=5
    · simp only [hv,ite_true,depthIndicator,bitSign_one,pow_one]
    · simp only [hv,ite_false,depthIndicator,bitSign_zero,pow_zero]
  rw [hi,← bitSign_add]
  congr 1
  ring

/-- Complete exact dyadic contribution to the original manuscript T,
including both depth-five indicators and the literal global w/z term. -/
theorem correctedDyadic_T_product (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) :
    correctedSign p hp P D 2*bitSign (B p+HasseObstructionArithmetic.P p)=bitSign (T p) := by
  rcases exact_T_branches p hp hL with h | h | h
  · rw [correctedSign_nonunit p hp hL P D h,one_mul]
    exact ((T_sign_branch_formulas p).1 h).symm
  · rw [correctedSign_unitOne p hp hL P D h.2]
    exact ((T_sign_branch_formulas p).2.1 h.1 h.2).symm
  · rw [correctedSign_unitFifteen p hp hL P D h.2]
    exact ((T_sign_branch_formulas p).2.2 h.1 h.2).symm

#print axioms correctedSign_unitOne
#print axioms correctedSign_unitFifteen
#print axioms correctedDyadic_T_product

end FourCorner.HasseFinalDyadic
