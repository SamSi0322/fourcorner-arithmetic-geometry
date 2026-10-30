import ThetaCoverClassPortable.MeromorphicComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
namespace FourCorner.MeromorphicFrames.Atlas
variable {X : Scheme} [IsIntegral X] {M N : X.Modules}
    {k : Type} [Field k] (c : X ⟶ Spec (.of k)) [IsProper c]

def tensor (A : Atlas M) (B : Atlas N) : Atlas (M⊗N) := by
  let AL := commonLeft A B c
  let BR := commonRight A B c
  refine {
    Index := A.Index × B.Index
    U := common A B
    cover := common_cover A B
    affine := common_affine A B c
    nonempty := common_nonempty A B
    frame := fun p=>tensorSections (AL.frame p) (BR.frame p)
    isFrame := fun p=>(AL.isFrame p).tensorSections (BR.isFrame p)
    q := fun p=>A.q p.1*B.q p.2
    q_ne_zero := fun p=>mul_ne_zero (A.q_ne_zero p.1) (B.q_ne_zero p.2)
    cocycle := AL.cocycle.mul BR.cocycle
    transition := ?_
    transition_field := ?_ }
  · intro p z
    rw [map_tensorSections,AL.transition,BR.transition,tensorSections_smul_left,tensorSections_smul_right,smul_smul]
    rw [map_tensorSections]
    rfl
  · intro p z
    letI := common_nonempty A B p
    letI := common_nonempty A B z
    letI : Nonempty ((common A B p ⊓ common A B z : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
    change algebraMap Γ(X,common A B p ⊓ common A B z) X.functionField
      (AL.cocycle.u p z*BR.cocycle.u p z)=_
    rw [map_mul,AL.transition_field,BR.transition_field]
    exact div_mul_div_comm _ _ _ _

#print axioms tensor
end FourCorner.MeromorphicFrames.Atlas
