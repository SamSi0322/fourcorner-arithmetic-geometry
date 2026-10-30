import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
namespace FourCorner.FiniteFibreCounting
open scoped BigOperators

/-- Disjoint boundary fibres plus exactly-two nonboundary fibres give the
literal counting identity; all actual fibre inputs are discharged by callers. -/
theorem boundary_and_two {α:Type*} [Fintype α] (β:α→Type*) [∀a,Finite (β a)]
    (P Q:α→Prop) (h:∀a,¬P a→Nat.card (β a)=if Q a then 2 else 0) :
    Nat.card (Σa,β a)=Nat.card (Σa:{a:α //P a},β a.val)+
      2*Nat.card {a:α //¬P a ∧ Q a} := by
  classical
  let e:{a:{a:α //¬P a} //Q a.val} ≃ {a:α //¬P a ∧ Q a} :=
    {toFun:=fun a=>⟨a.val.val,a.val.property,a.property⟩
     invFun:=fun a=>⟨⟨a.val,a.property.1⟩,a.property.2⟩
     left_inv:=by intro a;cases a;rfl
     right_inv:=by intro a;cases a;rfl}
  have hc:Nat.card {a:α //¬P a ∧ Q a}=
      (Finset.univ.filter (fun a:{a:α //¬P a}=>Q a.val)).card := by
    rw [←Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [Nat.card_sigma,Nat.card_sigma,←Fintype.sum_subtype_add_sum_subtype P (fun a=>Nat.card (β a))]
  congr 1
  calc
    (∑a:{a:α //¬P a},Nat.card (β a.val)) =
        ∑a:{a:α //¬P a},if Q a.val then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact h a.val a.property
    _=2*Nat.card {a:α //¬P a ∧ Q a} := by
      rw [hc,←Finset.sum_filter]
      simp [Finset.sum_const,nsmul_eq_mul,mul_comm]

end FourCorner.FiniteFibreCounting
#print axioms FourCorner.FiniteFibreCounting.boundary_and_two
