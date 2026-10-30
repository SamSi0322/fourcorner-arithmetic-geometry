import ThetaCoverClassPortable.ActualQuadraticTensorBaseChange

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourCorner.ActualSplitQuadratic
variable {K : Type} [Field K] [CharZero K] (c s : K) (hs : s^2=c) (hn : s≠0)

def positive : QuadraticAlgebra K c 0 →ₐ[K] K := QuadraticAlgebra.lift ⟨s,by
  rw [←pow_two,hs]
  simp [Algebra.smul_def]⟩
def negative : QuadraticAlgebra K c 0 →ₐ[K] K := QuadraticAlgebra.lift ⟨-s,by
  rw [←pow_two,neg_sq,hs]
  simp [Algebra.smul_def]⟩

def pairMap : QuadraticAlgebra K c 0 →ₐ[K] K×K :=
  (positive c s hs).prod (negative c s hs)

theorem pairMap_formula (z : QuadraticAlgebra K c 0) :
    pairMap c s hs z=(z.re+z.im*s,z.re-z.im*s) := by
  change (z.re • (1:K)+z.im • s,z.re • (1:K)+z.im • (-s))=_
  simp [Algebra.smul_def,sub_eq_add_neg]

include hn in
theorem pairMap_injective : Function.Injective (pairMap c s hs) := by
  intro z w h
  rw [pairMap_formula,pairMap_formula] at h
  have hp := congrArg Prod.fst h
  have hm := congrArg Prod.snd h
  apply QuadraticAlgebra.ext
  · linear_combination (1/2)*hp+(1/2)*hm
  · apply mul_right_cancel₀ hn
    linear_combination (1/2)*hp-(1/2)*hm

include hn in
theorem pairMap_surjective : Function.Surjective (pairMap c s hs) := by
  rintro ⟨u,v⟩
  refine ⟨⟨(u+v)/2,(u-v)/(2*s)⟩,?_⟩
  rw [pairMap_formula]
  apply Prod.ext <;> dsimp
  · field_simp [hn]
    ring
  · field_simp [hn]
    ring

def equivalence : QuadraticAlgebra K c 0 ≃ₐ[K] K×K :=
  AlgEquiv.ofBijective (pairMap c s hs) ⟨pairMap_injective c s hs hn,pairMap_surjective c s hs hn⟩

theorem equivalence_formula (z : QuadraticAlgebra K c 0) :
    equivalence c s hs hn z=(z.re+z.im*s,z.re-z.im*s) := pairMap_formula c s hs z

end FourCorner.ActualSplitQuadratic
