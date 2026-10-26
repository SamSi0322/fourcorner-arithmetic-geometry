import ProjectiveThreePoint
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option autoImplicit false
namespace FourCorner.HasseBranchConfiguration
open ProjectiveThreePoint
variable {K:Type*} [Field K]

def minusOne:Line K:=Projectivization.mk K ![-1,1]
 (by intro h;have:=congrFun h 1;simpa using this)
def parameterVector (p:K):V K:=![-(p+1),p-1]
lemma parameterVector_ne_zero (h2:(2:K)≠0) (p:K):parameterVector p≠0:=by
 intro h
 have h0:=congrFun h 0
 have h1:=congrFun h 1
 simp only [parameterVector,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Pi.zero_apply] at h0 h1
 apply h2
 linear_combination -h0-h1

def parameter (h2:(2:K)≠0) (p:K):Line K:=
 Projectivization.mk K (parameterVector p) (parameterVector_ne_zero h2 p)

/-- The moving literal branch point is injective in the original parameter.
Its determinant is 2; p=1 is retained as the actual infinity value. -/
theorem parameter_injective (h2:(2:K)≠0):Function.Injective (parameter h2):=by
 intro p q hpq
 obtain ⟨c,hc⟩:=(Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hpq
 have h0:=congrFun hc 0
 have h1:=congrFun hc 1
 change c*(-(q+1))= -(p+1) at h0
 change c*(q-1)=p-1 at h1
 have he:(2:K)*c=2:=by linear_combination -h0-h1
 have hc1:c=1:=mul_left_cancel₀ h2 (by simpa only [mul_one] using he)
 rw [hc1,one_mul] at h1
 exact sub_left_injective h1.symm

/-- The literal unordered five branch points, inside the native projective
line. No point set is replaced by a parameter label or a matrix normal form. -/
def branchSet (h2:(2:K)≠0) (p:K):Set (Line K):=
 {infinity,zero,one,minusOne,parameter h2 p}
lemma branchSet_finite (h2:(2:K)≠0) (p:K):(branchSet h2 p).Finite:=by
 simp only [branchSet,Set.finite_insert,Set.finite_singleton]

def frame (h2:(2:K)≠0) (p:K):Fin 4→Line K:=![infinity,zero,one,parameter h2 p]
lemma frame_mem (h2:(2:K)≠0) (p:K) (j:Fin 4):frame h2 p j∈branchSet h2 p:=by
 fin_cases j <;>simp [frame,branchSet]

def images (h2:(2:K)≠0) (g:V K≃ₗ[K]V K) (p:K):Fin 4→Line K:=fun j=>action g (frame h2 p j)

/-- Four image values determine the original parameter: the first three
fix the actual projective action and the fourth fixes the moving point. -/
theorem parameter_eq_of_images_eq (h2:(2:K)≠0) (g h:V K≃ₗ[K]V K) (p q:K)
 (he:images h2 g p=images h2 h q):p=q:=by
 have h0:=congrFun he 0
 have h1:=congrFun he 1
 have h2':=congrFun he 2
 have ha:action g=action h:=action_ext g h h0 h1 h2'
 have h3:=congrFun he 3
 change action g (parameter h2 p)=action h (parameter h2 q) at h3
 rw [←ha] at h3
 exact parameter_injective h2 (action_injective g h3)

/-- Genuine unordered branch-configuration equivalence under an arbitrary
GL2-induced projective action (all linear automorphisms of the native plane). -/
def Equivalent (h2:(2:K)≠0) (p q:K):Prop:=
 ∃g:V K≃ₗ[K]V K, action g '' branchSet h2 p=branchSet h2 q

/-- Each actual projective-equivalence fibre of this literal five-point
family is finite. The proof injects it into four values in the fixed finite
branch set, using the proved three-point uniqueness of the actual action. -/
theorem finite_parameter_fibre (h2:(2:K)≠0) (q:K):
 {p:K|Equivalent h2 p q}.Finite:=by
 classical
 let T:Type _:={p:K//Equivalent h2 p q}
 let witness:T→(V K≃ₗ[K]V K):=fun p=>Classical.choose p.property
 have hw (p:T):action (witness p) '' branchSet h2 p.val=branchSet h2 q:=Classical.choose_spec p.property
 let S:Type _:={x:Line K//x∈branchSet h2 q}
 let encode:T→(Fin 4→S):=fun p j=>⟨images h2 (witness p) p.val j,by
   rw [←hw p]
   exact ⟨frame h2 p.val j,frame_mem h2 p.val j,rfl⟩⟩
 have hinj:Function.Injective encode:=by
   intro p r he
   apply Subtype.ext
   apply parameter_eq_of_images_eq h2 (witness p) (witness r)
   funext j
   exact congrArg Subtype.val (congrFun he j)
 letI:Fintype S:=(branchSet_finite h2 q).fintype
 have ht:Finite T:=Finite.of_injective encode hinj
 exact @Set.toFinite K {p:K|Equivalent h2 p q} ht

#print axioms parameter_injective
#print axioms finite_parameter_fibre
end FourCorner.HasseBranchConfiguration
