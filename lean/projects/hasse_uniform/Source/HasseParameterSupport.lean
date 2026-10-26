import HasseGoodUnitRow

/-! A genuine source point removes every extraneous prime of the rational
tangent coefficient from the global product, leaving the exact finite
parameter support. No bad-prime evaluation is assumed. -/
namespace FourCorner.HasseParameterSupport

open HasseObstructionArithmetic HasseHilbertArithmetic HasseTangentGlobal
open HasseRationalSource HasseAnchorChoice HasseGoodUnitRow

def parameterSupport (p : ℚ) : Finset ℕ :=
  {0,2} ∪ rationalSupport p ∪ rationalSupport (p-1) ∪ rationalSupport (p+1)

def oddParameterSupport (p : ℚ) : Finset ℕ := ((parameterSupport p).erase 0).erase 2

/-- All non-parameter primes, including primes of tangent contact of any
depth, give trivial sign on the actual rational source tangent coefficient. -/
theorem tangentSign_one_outside_parameter_support (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (q : ℕ)
    (h : q ∉ parameterSupport p) : tangentSign p hp P D q=1 := by
  have hq : q≠0 ∧ q≠2 ∧ q∉rationalSupport p ∧ q∉rationalSupport (p-1) ∧ q∉rationalSupport (p+1) := by
    simpa only [parameterSupport,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      not_or,and_assoc] using h
  by_cases hprime : q.Prime
  · have hp0 : p ≠ 0 := by linarith
    have ha0 : p-1 ≠ 0 := by linarith
    have hb0 : p+1 ≠ 0 := by linarith
    exact tangentSign_good_unit ⟨q,hprime,hq.2.1⟩ p hp P D
      (valuation_zero_outside_support p hp0 q hprime hq.2.2.1)
      (valuation_zero_outside_support (p-1) ha0 q hprime hq.2.2.2.1)
      (valuation_zero_outside_support (p+1) hb0 q hprime hq.2.2.2.2)
  · exact rationalSign_one_of_not_prime _ _ _ _ q hq.1 hq.2.1 hprime

/-- Global reciprocity on precisely the finite parameter support. This
proves that no anchor-coordinate or tangent-contact primes were omitted. -/
theorem tangentSign_parameter_product (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) :
    (∏ v ∈ parameterSupport p,tangentSign p hp P D v)=1 := by
  let S := allSupport p P D
  let T := parameterSupport p
  have hleft : (∏ v ∈ S ∪ T,tangentSign p hp P D v)=(∏ v ∈ S,tangentSign p hp P D v) := by
    symm
    apply Finset.prod_subset Finset.subset_union_left
    intro v hv hn
    exact tangentSign_one_outside_support p hp P D v hn
  have hright : (∏ v ∈ S ∪ T,tangentSign p hp P D v)=(∏ v ∈ T,tangentSign p hp P D v) := by
    symm
    apply Finset.prod_subset Finset.subset_union_right
    intro v hv hn
    exact tangentSign_one_outside_parameter_support p hp P D v hn
  exact hright.symm.trans (hleft.trans (tangentSign_global_product p hp P D))

theorem tangentSign_parameter_finite_product (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) :
    tangentSign p hp P D 2*(∏ q ∈ oddParameterSupport p,tangentSign p hp P D q)= -1 := by
  have h0 : 0∈parameterSupport p := by simp [parameterSupport]
  have h2 : 2∈(parameterSupport p).erase 0 := by simp [parameterSupport]
  have he := Finset.mul_prod_erase (parameterSupport p) (tangentSign p hp P D) h0
  have he2 := Finset.mul_prod_erase ((parameterSupport p).erase 0) (tangentSign p hp P D) h2
  rw [tangentSign_real p hp P D,tangentSign_parameter_product p hp P D] at he
  dsimp [oddParameterSupport]
  rw [he2]
  linarith

#print axioms tangentSign_one_outside_parameter_support
#print axioms tangentSign_parameter_product
#print axioms tangentSign_parameter_finite_product

end FourCorner.HasseParameterSupport
