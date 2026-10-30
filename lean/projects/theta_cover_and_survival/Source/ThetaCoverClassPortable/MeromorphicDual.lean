import ThetaCoverClassPortable.MeromorphicFrames
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_dual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
namespace FourCorner.MeromorphicFrames.Atlas
variable {X : Scheme} [IsIntegral X] {M : X.Modules} (A : Atlas M)

lemma dualFrame_exists (i : A.Index) : ∃t : Γ(Scheme.Modules.dual M,A.U i),
    IsFrameOn t (A.U i) ∧ ihomEval M (𝟙_ X.Modules) (A.U i) (A.frame i) t=unitSection (A.U i) := by
  obtain ⟨t,ht,he⟩ := (A.isFrame i).exists_isFrameOn_dual (le_refl (A.U i))
  have hr : M.presheaf.map (homOfLE (le_refl (A.U i))).op (A.frame i)=A.frame i := by
    rw [Subsingleton.elim (homOfLE (le_refl (A.U i))) (𝟙 (A.U i)),op_id,M.presheaf.map_id]
    rfl
  exact ⟨t,ht,by rwa [hr] at he⟩

def dualFrame (i : A.Index) : Γ(Scheme.Modules.dual M,A.U i) := (dualFrame_exists A i).choose
lemma dualFrame_isFrame (i : A.Index) : IsFrameOn (dualFrame A i) (A.U i) := (dualFrame_exists A i).choose_spec.1
lemma dualFrame_eval (i : A.Index) :
    ihomEval M (𝟙_ X.Modules) (A.U i) (A.frame i) (dualFrame A i)=unitSection (A.U i) :=
  (dualFrame_exists A i).choose_spec.2

lemma dualFrame_eval_res (i : A.Index) {V : X.Opens} (h : V≤A.U i) :
    ihomEval M (𝟙_ X.Modules) V (M.presheaf.map (homOfLE h).op (A.frame i))
      ((Scheme.Modules.dual M).presheaf.map (homOfLE h).op (dualFrame A i))=unitSection V := by
  rw [←map_ihomEval,dualFrame_eval,map_unitSection]

def dualCocycle : UnitCocycle A.U :=
  (exists_unitCocycle_map_eq_smul_of_isFrameOn (dualFrame A) (dualFrame_isFrame A)).choose
lemma dual_transition (i j : A.Index) :
    (Scheme.Modules.dual M).presheaf.map (homOfLE (inf_le_right : A.U i ⊓ A.U j ≤ A.U j)).op (dualFrame A j)=
      (dualCocycle A).u i j • (Scheme.Modules.dual M).presheaf.map (homOfLE inf_le_left).op (dualFrame A i) :=
  (exists_unitCocycle_map_eq_smul_of_isFrameOn (dualFrame A) (dualFrame_isFrame A)).choose_spec i j

lemma dual_coefficient_inverse (i j : A.Index) : A.cocycle.u i j*(dualCocycle A).u i j=1 := by
  have he := dualFrame_eval_res A j (V:=A.U i ⊓ A.U j) inf_le_right
  rw [A.transition,dual_transition,ihomEval_smul_left,ihomEval_smul_right,
    dualFrame_eval_res,smul_smul] at he
  change A.cocycle.u i j*(dualCocycle A).u i j*1=1 at he
  simpa only [mul_one] using he

/-- True dual local frames and their actual inverse meromorphic values. -/
abbrev dual : Atlas (Scheme.Modules.dual M) where
  Index := A.Index
  U := A.U
  cover := A.cover
  affine := A.affine
  nonempty := A.nonempty
  frame := dualFrame A
  isFrame := dualFrame_isFrame A
  q i := (A.q i)⁻¹
  q_ne_zero i := inv_ne_zero (A.q_ne_zero i)
  cocycle := dualCocycle A
  transition := dual_transition A
  transition_field i j := by
    letI := A.nonempty i
    letI := A.nonempty j
    letI : Nonempty ((A.U i ⊓ A.U j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
    have he := congrArg (algebraMap Γ(X,A.U i ⊓ A.U j) X.functionField) (dual_coefficient_inverse A i j)
    rw [map_mul,map_one,A.transition_field] at he
    rw [←inv_eq_of_mul_eq_one_right he,inv_div,inv_div_inv]

#print axioms dual
end FourCorner.MeromorphicFrames.Atlas
