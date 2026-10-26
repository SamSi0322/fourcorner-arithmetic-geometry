import CriticalRadicalField
import CriticalFieldCoordinates
import CriticalProductSquareclass

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace FourCorner.CriticalOriginalFieldEquiv
open CriticalRadicalField Polynomial
variable (k : Type*) [Field k]

/-- All THREE literal original functions generate the actual accepted
radical field over its original constants. -/
theorem original_generate (i : k) :
    IntermediateField.adjoin k (Set.range ![a k i,b k i,c k i])=⊤ := by
  let S:=IntermediateField.adjoin k (Set.range ![a k i,b k i,c k i])
  have ha : a k i∈S := IntermediateField.subset_adjoin k _ ⟨0,rfl⟩
  have hb : b k i∈S := IntermediateField.subset_adjoin k _ ⟨1,rfl⟩
  have hc : c k i∈S := IntermediateField.subset_adjoin k _ ⟨2,rfl⟩
  have hp (p : k[X]) : polynomialValue k i p∈S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
    | monomial n z =>
      rw [←Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,polynomialValue_C,polynomialValue_X]
      exact S.mul_mem (S.algebraMap_mem z) (S.toSubalgebra.pow_mem ha n)
  have hbase (r : RatFunc k) : algebraMap (RatFunc k) (field k i) r∈S := by
    obtain ⟨p,q,hq,rfl⟩:=IsFractionRing.div_surjective k[X] r
    rw [map_div₀]
    exact S.div_mem (hp p) (hp q)
  let T : Subalgebra (RatFunc k) (field k i) :=
    { S.toSubfield.toSubring with algebraMap_mem' := hbase }
  have ht : Algebra.adjoin (RatFunc k) {b k i,c k i}≤T := by
    apply Algebra.adjoin_le
    intro z hz
    rcases hz with rfl|rfl
    · exact hb
    · exact hc
  dsimp only [b,c] at ht
  rw [Biquadratic.roots_generate_algebra (RatFunc k) (radicandB k i) (radicandC k i)] at ht
  apply top_unique
  intro z _
  exact ht (show z∈(⊤ : Subalgebra (RatFunc k) (field k i)) by trivial)

/-- The independent E function field is identified with the SAME original
literal (a,b,c) radical field, with no supplied comparison or genus. -/
def equiv (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    CriticalEllipticField.field k ≃ₐ[k] field k i :=
  CriticalFieldEquivalence.equiv i hi h2 (a k i) (b k i) (c k i)
    (actual_critical_equations k i).1
    (by simpa only [map_add,map_one] using (actual_critical_equations k i).2)
    (a_transcendental k i) (original_generate k i)

theorem equiv_x (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    equiv k i hi h2 (CriticalEllipticField.x k)=
      CriticalDirectMap.x (algebraMap k (field k i) i) (a k i) (b k i) (c k i) := by
  exact CriticalFieldEquivalence.equiv_x i hi h2 (a k i) (b k i) (c k i)
    (actual_critical_equations k i).1
    (by simpa only [map_add,map_one] using (actual_critical_equations k i).2)
    (a_transcendental k i) (original_generate k i)

end FourCorner.CriticalOriginalFieldEquiv
#print axioms FourCorner.CriticalOriginalFieldEquiv.original_generate
#print axioms FourCorner.CriticalOriginalFieldEquiv.equiv
#print axioms FourCorner.CriticalOriginalFieldEquiv.equiv_x
