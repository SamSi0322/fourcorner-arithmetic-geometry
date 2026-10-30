import ThetaCoverClassPortable.KummerRegularUnits
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_mul_iso_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_twist_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_trivial_iso_tensorUnit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle
namespace FourCorner.KummerUnitCocycle
variable {X : Scheme} [IsIntegral X]

lemma germ_res {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) (f : Γ(X,U)) :
    algebraMap Γ(X,V) X.functionField (rO h f)=algebraMap Γ(X,U) X.functionField f := by
  exact X.presheaf.germ_res_apply (homOfLE h) _ _ f

/-- The units are ACTUAL regular sections, recovered from native field roots
using affine normality. The root ratios are not added as regularity premises. -/
theorem ratio_regular {k : Type} [Field k] (c : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 c] {U V : X.Opens}
    (hUV : IsAffineOpen (U ⊓ V)) [Nonempty U] [Nonempty V] [Nonempty ((U ⊓ V : X.Opens) : Scheme)]
    (h : X.functionField) (q r : X.functionField) (qh : q≠0)
    (a : Γ(X,U)ˣ) (b : Γ(X,V)ˣ)
    (ha : algebraMap Γ(X,U) X.functionField (a:Γ(X,U))=q^2*h)
    (hb : algebraMap Γ(X,V) X.functionField (b:Γ(X,V))=r^2*h) :
    ∃u : Γ(X,U ⊓ V)ˣ,algebraMap Γ(X,U ⊓ V) X.functionField (u:Γ(X,U ⊓ V))=r/q := by
  have hh : h≠0 := by
    intro hh
    have hz : algebraMap Γ(X,U) X.functionField (a:Γ(X,U))=0 := by rw [ha,hh,mul_zero]
    exact (a.isUnit.map (algebraMap Γ(X,U) X.functionField)).ne_zero hz
  let w : Γ(X,U ⊓ V)ˣ := (Units.map (rO inf_le_right).toMonoidHom b)*(Units.map (rO inf_le_left).toMonoidHom a)⁻¹
  apply KummerRegularUnits.square_unit_regular c (U ⊓ V) hUV (r/q) w
  change algebraMap Γ(X,U ⊓ V) X.functionField
    ((rO inf_le_right (b:Γ(X,V)))*(rO inf_le_left (↑a⁻¹:Γ(X,U))))=(r/q)^2
  rw [map_mul,germ_res,germ_res]
  have hai : algebraMap Γ(X,U) X.functionField (↑a⁻¹:Γ(X,U))=
      (algebraMap Γ(X,U) X.functionField (a:Γ(X,U)))⁻¹ := by
    exact map_units_inv _ a
  rw [hai,ha,hb]
  field_simp
  <;> ring

lemma nonempty_inf (U V : X.Opens) [Nonempty U] [Nonempty V] :
    Nonempty ((U ⊓ V : X.Opens) : Scheme) := by
  refine ⟨⟨genericPoint X,?_,?_⟩⟩
  · exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance : Nonempty U))
  · exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using (inferInstance : Nonempty V))

section Atlas
variable {k : Type} [Field k] (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
    {ι : Type} (U : ι → X.Opens) [∀i,Nonempty (U i)]
    (hAff : ∀i j,IsAffineOpen (U i ⊓ U j)) (h : X.functionField)
    (q : ι → X.functionField) (a : ∀i,Γ(X,U i)ˣ)
    (ha : ∀i,algebraMap Γ(X,U i) X.functionField (a i:Γ(X,U i))=q i^2*h)

include U h a ha in
lemma root_ne_zero (i : ι) : q i≠0 := by
  intro hz
  have he : algebraMap Γ(X,U i) X.functionField (a i:Γ(X,U i))=0 := by rw [ha i,hz,zero_pow (by decide : 2≠0),zero_mul]
  exact ((a i).isUnit.map (algebraMap Γ(X,U i) X.functionField)).ne_zero he

local instance pair_nonempty (i j : ι) : Nonempty ((U i ⊓ U j : X.Opens) : Scheme) := nonempty_inf _ _

def transition (i j : ι) : Γ(X,U i ⊓ U j)ˣ :=
  (ratio_regular c (hAff i j) h (q i) (q j) (root_ne_zero U h q a ha i) (a i) (a j) (ha i) (ha j)).choose

lemma transition_field (i j : ι) :
    algebraMap Γ(X,U i ⊓ U j) X.functionField (transition c U hAff h q a ha i j:Γ(X,U i ⊓ U j))=q j/q i :=
  (ratio_regular c (hAff i j) h (q i) (q j) (root_ne_zero U h q a ha i) (a i) (a j) (ha i) (ha j)).choose_spec

/-- Genuine regular unit transition cocycle with the literal q_j/q_i
inside the native function field. -/
def cocycle : UnitCocycle U where
  u i j := transition c U hAff h q a ha i j
  refl i := by
    apply (X.germToFunctionField_injective (U i ⊓ U i))
    change algebraMap Γ(X,U i ⊓ U i) X.functionField _ = _
    rw [transition_field,map_one,div_self (root_ne_zero U h q a ha i)]
  cocycle i j l := by
    letI : Nonempty ((U i ⊓ U j ⊓ U l : X.Opens) : Scheme) := nonempty_inf _ _
    apply (X.germToFunctionField_injective (U i ⊓ U j ⊓ U l))
    change algebraMap Γ(X,U i ⊓ U j ⊓ U l) X.functionField _ = algebraMap Γ(X,U i ⊓ U j ⊓ U l) X.functionField _
    rw [map_mul,germ_res,germ_res,germ_res,transition_field,transition_field,transition_field]
    field_simp [root_ne_zero U h q a ha i,root_ne_zero U h q a ha j]
    <;> ring

end Atlas

#print axioms ratio_regular
end FourCorner.KummerUnitCocycle
