import HasseMatrixBranchFiniteness

noncomputable section
set_option autoImplicit false
namespace FourCorner.HasseOrderedBranchBridge
open ProjectiveThreePoint HasseBranchConfiguration
variable {K:Type*} [Field K]

/-- Order matching the literal diagonal-net coefficients: 0,1,-1,lambda,infinity. -/
def ordered (h2:(2:K)≠0) (p:K):Fin 5→Line K:=![zero,one,minusOne,parameter h2 p,infinity]

lemma range_ordered (h2:(2:K)≠0) (p:K):Set.range (ordered h2 p)=branchSet h2 p:=by
 ext x
 constructor
 · rintro ⟨j,rfl⟩
   fin_cases j <;>simp [ordered,branchSet]
 · intro hx
   simp only [branchSet,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
   rcases hx with h|h|h|h|h
   · exact ⟨4,h.symm⟩
   · exact ⟨0,h.symm⟩
   · exact ⟨1,h.symm⟩
   · exact ⟨2,h.symm⟩
   · exact ⟨3,h.symm⟩

/-- A genuine induced projective action matching all five original points
up to ANY permutation gives exactly the unordered equivalence used in the
finite-fibre theorem. No permutation or matrix form is preselected. -/
theorem equivalent_of_ordered_perm (h2:(2:K)≠0) (p q:K) (g:V K≃ₗ[K]V K)
 (σ:Equiv.Perm (Fin 5)) (he:∀j,action g (ordered h2 p j)=ordered h2 q (σ j)):
 Equivalent h2 p q:=by
 refine ⟨g,?_⟩
 rw [←range_ordered h2 p,←range_ordered h2 q]
 ext x
 constructor
 · rintro ⟨_,⟨j,rfl⟩,rfl⟩
   exact ⟨σ j,(he j).symm⟩
 · rintro ⟨j,rfl⟩
   refine ⟨ordered h2 p (σ.symm j),⟨σ.symm j,rfl⟩,?_⟩
   simpa only [Equiv.apply_symm_apply] using he (σ.symm j)

#print axioms equivalent_of_ordered_perm
end FourCorner.HasseOrderedBranchBridge
