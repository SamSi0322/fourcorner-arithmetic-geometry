import ProjectiveThreePoint

noncomputable section
set_option autoImplicit false
namespace FourCorner.ProjectiveActionFinite
open ProjectiveThreePoint
variable {K:Type*} [Field K]

def IsProjectiveAction (f:Line K→Line K):Prop:=∃g:V K≃ₗ[K]V K,f=action g

def triple (f:Line K→Line K):Fin 3→Line K:=![f infinity,f zero,f one]

/-- Only finitely many genuine GL2-induced projective actions can send the
three specified native points into a fixed finite set. Matrices themselves
are not counted, since all nonzero scalar multiples induce the same action. -/
theorem finite_actions_to_finite (S:Set (Line K)) (hS:S.Finite):
 {f:Line K→Line K|IsProjectiveAction f ∧∀j:Fin 3,triple f j∈S}.Finite:=by
 classical
 let T:Type _:={f:Line K→Line K//IsProjectiveAction f ∧∀j:Fin 3,triple f j∈S}
 let A:Type _:={x:Line K//x∈S}
 let encode:T→(Fin 3→A):=fun f j=>⟨triple f.val j,f.property.2 j⟩
 have hinj:Function.Injective encode:=by
  intro f h he
  apply Subtype.ext
  obtain ⟨g,hg⟩:=f.property.1
  obtain ⟨g',hg'⟩:=h.property.1
  rw [hg,hg']
  apply action_ext
  · have hh:=congrArg Subtype.val (congrFun he 0)
    change f.val infinity=h.val infinity at hh
    simpa only [hg,hg'] using hh
  · have hh:=congrArg Subtype.val (congrFun he 1)
    change f.val zero=h.val zero at hh
    simpa only [hg,hg'] using hh
  · have hh:=congrArg Subtype.val (congrFun he 2)
    change f.val one=h.val one at hh
    simpa only [hg,hg'] using hh
 letI:Fintype A:=hS.fintype
 have ht:Finite T:=Finite.of_injective encode hinj
 exact @Set.toFinite _ _ ht

#print axioms finite_actions_to_finite
end FourCorner.ProjectiveActionFinite
