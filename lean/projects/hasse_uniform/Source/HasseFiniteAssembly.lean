import HasseWR
import HasseConstantOdd

namespace FourCorner.HasseFiniteAssembly

open HasseObstructionArithmetic HasseParameterSupport HasseInertParity HasseSignAlgebra HasseWR

noncomputable def poleTerm (p : ℚ) (q : ℕ) : ZMod 2 := by
  classical
  exact if q≠2 ∧ padicValRat q p<0 ∧ Odd (padicValRat q p) then sigma q else 0

noncomputable def expectedOddBit (p : ℚ) (q : ℕ) : ZMod 2 := positiveTerm (p+1) q+poleTerm p q

theorem poleSum_on_parameter_support (p : ℚ) (hp : 1<p) :
    P p=∑ q ∈ oddParameterSupport p,poleTerm p q := by
  classical
  let F := (rationalSupport p).filter (fun q => q≠2 ∧ padicValRat q p<0 ∧ Odd (padicValRat q p))
  have hF : F ⊆ oddParameterSupport p := by
    intro q hq
    have hh := Finset.mem_filter.mp hq
    have hprime := prime_of_rationalSupport p q hh.1
    simp only [oddParameterSupport,Finset.mem_erase]
    exact ⟨hh.2.1,hprime.ne_zero,by simp [parameterSupport,hh.1]⟩
  have he : P p=∑ q ∈ F,poleTerm p q := by
    change (∑ q ∈ F,sigma q)= _
    apply Finset.sum_congr rfl
    intro q hq
    simp only [poleTerm,if_pos (Finset.mem_filter.mp hq).2]
  rw [he]
  apply Finset.sum_subset hF
  intro q hq hn
  by_cases hc : q≠2 ∧ padicValRat q p<0 ∧ Odd (padicValRat q p)
  · have hnot : q∉rationalSupport p := by
      intro hh
      exact hn (Finset.mem_filter.mpr ⟨hh,hc⟩)
    have hv := valuation_zero_outside_support p (by linarith) q (oddParameterSupport_prime p q hq).1 hnot
    exact False.elim (by rw [hv] at hc; omega)
  · simp only [poleTerm,if_neg hc]

/-- The odd corrected valuation/character labels sum to exactly B+P,
including every finite support prime and every negative-depth pole. -/
theorem expectedOddBit_sum (p : ℚ) (hp : 1<p) :
    (∑ q ∈ oddParameterSupport p,expectedOddBit p q)=B p+P p := by
  classical
  simp only [expectedOddBit,Finset.sum_add_distrib]
  rw [← poleSum_on_parameter_support p hp]
  have hb := halfInertSum_on_parameter_support p (p+1) (by linarith)
    (by intro q hq; simp [parameterSupport,hq])
  change (∑ q ∈ oddParameterSupport p,positiveTerm (p+1) q)+P p=halfInertSum (p+1)+P p
  rw [← hb]

theorem expectedOddSign_product (p : ℚ) (hp : 1<p) :
    (∏ q ∈ oddParameterSupport p,bitSign (expectedOddBit p q))=bitSign (B p+P p) := by
  rw [← bitSign_sum,expectedOddBit_sum p hp]

def depthIndicator (v : ℤ) : ZMod 2 := if v=5 then 1 else 0

theorem f2_unit_fifteen_cancel (a b c i : ZMod 2) : (i+a+b)+(b+c)=i+a+c := by
  have hbb : b+b=0 := (by decide : ∀ x : ZMod 2,x+x=0) b
  calc
    _=i+a+(b+b)+c := by ring
    _=_ := by rw [hbb];ring

/-- Final F2 arithmetic of the three exact T branches. This statement
contains only the literal parameter bits; local evaluations are not assumed. -/
theorem T_sign_branch_formulas (p : ℚ) :
    (padicValRat 2 p ≠ 0 → bitSign (T p)=bitSign (B p+P p)) ∧
    (padicValRat 2 p=0 → UnitOne p →
      bitSign (T p)=bitSign (depthIndicator (padicValRat 2 (p-1)))*bitSign (B p+P p)) ∧
    (padicValRat 2 p=0 → UnitFifteen p →
      bitSign (T p)=bitSign (depthIndicator (padicValRat 2 (p+1))+A p+B p)*bitSign (B p+P p)) := by
  refine ⟨?_,?_,?_⟩
  · intro hv
    rw [T_nonunit p hv]
  · intro hv h
    rw [T_unit_one p hv h,← bitSign_add]
    simp only [depthIndicator,add_assoc]
  · intro hv h
    rw [T_unit_fifteen p hv h,← bitSign_add,f2_unit_fifteen_cancel]
    rfl

#print axioms expectedOddBit_sum
#print axioms expectedOddSign_product
#print axioms T_sign_branch_formulas

end FourCorner.HasseFiniteAssembly
