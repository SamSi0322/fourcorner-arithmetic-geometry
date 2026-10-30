import ThetaCoverClassPortable.KummerUnitCocycle

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle
namespace FourCorner.KummerSquareLine
variable {X : Scheme} [IsIntegral X]

lemma iso_inv_app_hom_app {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (s : Γ(M,U)) :
    e.inv.app U (e.hom.app U s)=s := by
  rw [←CategoryTheory.comp_apply,←Scheme.Modules.Hom.comp_app,e.hom_inv_id,Scheme.Modules.Hom.id_app]
  rfl

lemma isFrameOn_unit_smul {U : X.Opens} (a : Γ(X,U)ˣ) :
    IsFrameOn ((a:Γ(X,U)) • unitSection U) U := by
  intro W hWU _
  let b : Γ(X,W)ˣ := Units.map (rO hWU).toMonoidHom a
  have he : (fun r : Γ(X,W) => r • (𝟙_ X.Modules).presheaf.map (homOfLE hWU).op
      ((a:Γ(X,U)) • unitSection U))=
      (fun r : Γ(X,W) => r • unitSection W) ∘ (fun r => r*(b:Γ(X,W))) := by
    funext r
    rw [Scheme.Modules.map_smul,map_unitSection,smul_smul]
    rfl
  rw [he]
  exact smul_unitSection_bijective.comp (Units.mulRight_bijective b)

section Atlas
variable {k : Type} [Field k] (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
    {ι : Type} (U : ι → X.Opens) [∀i,Nonempty (U i)]
    (hAff : ∀i j,IsAffineOpen (U i ⊓ U j)) (h : X.functionField)
    (q : ι → X.functionField) (a : ∀i,Γ(X,U i)ˣ)
    (ha : ∀i,algebraMap Γ(X,U i) X.functionField (a i:Γ(X,U i))=q i^2*h)
local notation "cc" => KummerUnitCocycle.cocycle c U hAff h q a ha
local instance pair_nonempty (i j : ι) : Nonempty ((U i ⊓ U j : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _

lemma square_transition (i j : ι) :
    rO (inf_le_right : U i ⊓ U j ≤ U j) (a j:Γ(X,U j))=
      ((cc).mul cc).u i j*rO inf_le_left (a i:Γ(X,U i)) := by
  apply X.germToFunctionField_injective (U i ⊓ U j)
  change algebraMap Γ(X,U i ⊓ U j) X.functionField _ = algebraMap Γ(X,U i ⊓ U j) X.functionField _
  change algebraMap Γ(X,U i ⊓ U j) X.functionField _ =
    algebraMap Γ(X,U i ⊓ U j) X.functionField
      ((KummerUnitCocycle.transition c U hAff h q a ha i j:Γ(X,U i ⊓ U j)) *
       (KummerUnitCocycle.transition c U hAff h q a ha i j:Γ(X,U i ⊓ U j))*_)
  rw [map_mul,map_mul,KummerUnitCocycle.germ_res,KummerUnitCocycle.germ_res,
    KummerUnitCocycle.transition_field,ha i,ha j]
  field_simp [KummerUnitCocycle.root_ne_zero U h q a ha i]
  <;> ring

/-- Actual tensor-square trivialization; its value on each true local frame
is the original unit q_i²h, fixing the literal Kummer square pairing. -/
theorem exists_square_trivialization (hU : ⨆i,U i=⊤) :
    ∃e : (glueOfCocycle cc ⊗ glueOfCocycle cc) ≅ 𝟙_ X.Modules,
      ∀i,e.hom.app (U i) (tensorSections (glueFrame cc i) (glueFrame cc i))=
        (a i:Γ(X,U i)) • unitSection (U i) := by
  obtain ⟨e,he⟩ := exists_glueOfCocycle_mul_iso_tensor hU cc cc
  obtain ⟨v,hv⟩ := exists_iso_glueOfCocycle_app_eq_glueFrame hU ((cc).mul cc)
    (M:=𝟙_ X.Modules) (fun i=>(a i:Γ(X,U i)) • unitSection (U i))
    (fun i=>isFrameOn_unit_smul (a i)) (fun i j=>by
      rw [Scheme.Modules.map_smul,Scheme.Modules.map_smul,map_unitSection,map_unitSection,smul_smul]
      rw [square_transition c U hAff h q a ha i j])
  refine ⟨e.symm ≪≫ v.symm,fun i=>?_⟩
  change v.inv.app (U i) (e.inv.app (U i) (tensorSections (glueFrame cc i) (glueFrame cc i)))=_
  rw [←he i,iso_inv_app_hom_app,←hv i,iso_inv_app_hom_app]

end Atlas
#print axioms exists_square_trivialization
end FourCorner.KummerSquareLine
