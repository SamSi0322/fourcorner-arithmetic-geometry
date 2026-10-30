import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_AffineLimit
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_FGSubalgebraTensorStage
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf

set_option autoImplicit false

universe u v w

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.mapPresheaf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover AffineLimit.IsLFPInj FGSubalgebra.tensorStage FGSubalgebra.tensorStageMap FGSubalgebra.tensorStageToColimit FGSubalgebra.tensorStageToColimit_comp FGSubalgebra.tensorStageToColimit_surj FGSubalgebra.tensorStageToColimit_zero FGSubalgebra RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.setoid relPicardPresheaf LFP.stageHom"
namespace LFP
p2m_export "AlgebraicGeometry.RelPicard.LFP" "stageHom stageHom_val"
p2m_open "AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem exists_sectionsOf_linearEquiv_of_iso
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {L L' : X.Modules} (ψ : L ≅ L') :
    ∃ (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] (𝒱.sectionsOf c L').M0)
      (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] (𝒱.sectionsOf c L').M1)
      (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01] (𝒱.sectionsOf c L').M01),
      (∀ m, e01 ((𝒱.sectionsOf c L).r0 m) = (𝒱.sectionsOf c L').r0 (e0 m)) ∧
      (∀ m, e01 ((𝒱.sectionsOf c L).r1 m) = (𝒱.sectionsOf c L').r1 (e1 m)) ∧
      (∀ m, e0 m = (ψ.hom.app 𝒱.U0).hom m) ∧ (∀ m, e1 m = (ψ.hom.app 𝒱.U1).hom m) ∧
      (∀ m, e01 m = (ψ.hom.app (𝒱.U0 ⊓ 𝒱.U1)).hom m) := by

  let eU : ∀ U : X.Opens, Γ(L, U) ≃ₗ[Γ(X, U)] Γ(L', U) := fun U =>
    { toFun := fun m => (ψ.hom.app U).hom m
      invFun := fun m => (ψ.inv.app U).hom m
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r m => Scheme.Modules.Hom.app_smul ψ.hom r m
      left_inv := fun m => by
        change (ψ.hom.app U ≫ ψ.inv.app U).hom m = m
        rw [← Scheme.Modules.Hom.comp_app, ψ.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
      right_inv := fun m => by
        change (ψ.inv.app U ≫ ψ.hom.app U).hom m = m
        rw [← Scheme.Modules.Hom.comp_app, ψ.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl }

  have nat : ∀ {U V : X.Opens} (i : V ⟶ U) (m : Γ(L, U)),
      (ψ.hom.app V).hom (L.presheaf.map i.op m) = L'.presheaf.map i.op ((ψ.hom.app U).hom m) := by
    intro U V i m
    have := congr($((Scheme.Modules.Hom.mapPresheaf ψ.hom).naturality i.op) m)
    simp only [Scheme.Modules.mapPresheaf_app, CategoryTheory.ConcreteCategory.comp_apply] at this
    exact this
  refine ⟨eU 𝒱.U0, eU 𝒱.U1, eU (𝒱.U0 ⊓ 𝒱.U1), ?_, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · intro m; exact nat (homOfLE inf_le_left) m
  · intro m; exact nat (homOfLE inf_le_right) m

end AlgebraicGeometry.RelPicard.LFP

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.mapPresheaf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover AffineLimit.IsLFPInj FGSubalgebra.tensorStage FGSubalgebra.tensorStageMap FGSubalgebra.tensorStageToColimit FGSubalgebra.tensorStageToColimit_comp FGSubalgebra.tensorStageToColimit_surj FGSubalgebra.tensorStageToColimit_zero FGSubalgebra RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.setoid relPicardPresheaf LFP.stageHom"
namespace LFP
p2m_export "AlgebraicGeometry.RelPicard.LFP" "stageHom stageHom_val"
p2m_open "AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.RelPicard AlgebraicGeometry"

section ActR

variable (k : Type*) [CommRing k] {Γ : Type*} [CommRing Γ] [Algebra k Γ]
  (A' : Type*) [CommRing A'] [Algebra k A']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]

noncomputable def actR (s : Γ) : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P :=
  (DistribSMul.toLinearMap k P s).baseChange A'

@[scoped simp] theorem actR_tmul (s : Γ) (a : A') (m : P) :
    actR k A' s (a ⊗ₜ[k] m) = a ⊗ₜ[k] (s • m) := by
  simp [actR, DistribSMul.toLinearMap_apply]

theorem actR_one : actR k A' (1 : Γ) = (LinearMap.id : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P) := by
  ext m; simp

theorem actR_mul (s t : Γ) : actR k A' (P := P) (s * t) = actR k A' s ∘ₗ actR k A' t := by
  ext m; simp [mul_smul]

theorem actR_add (s t : Γ) : actR k A' (P := P) (s + t) = actR k A' s + actR k A' t := by
  ext m; simp [add_smul, tmul_add]

theorem rTensor_actR {A'' : Type*} [CommRing A''] [Algebra k A''] (h : A' →ₐ[k] A'') (s : Γ)
    (x : A' ⊗[k] P) :
    h.toLinearMap.rTensor P (actR k A' s x) = actR k A'' s (h.toLinearMap.rTensor P x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp [hx, hy]

theorem rTensor_smul' {A'' : Type*} [CommRing A''] [Algebra k A''] (h : A' →ₐ[k] A'')
    {Q : Type*} [AddCommGroup Q] [Module k Q] (a : A') (x : A' ⊗[k] Q) :
    h.toLinearMap.rTensor Q (a • x) = h a • h.toLinearMap.rTensor Q x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy]

theorem tmul_eq_smul_one_tmul {Q : Type*} [AddCommGroup Q] [Module k Q] (a : A') (m : Q) :
    a ⊗ₜ[k] m = a • ((1 : A') ⊗ₜ[k] m) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end ActR

section Intertwines

variable {k : Type*} [CommRing k] {Γ Γ' Γ'' : Type*} [CommRing Γ] [Algebra k Γ] [CommRing Γ'] [Algebra k Γ']
  [CommRing Γ''] [Algebra k Γ'']
  {A' : Type*} [CommRing A'] [Algebra k A']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {Q : Type*} [AddCommGroup Q] [Module Γ' Q] [Module k Q] [IsScalarTower k Γ' Q]
  {N : Type*} [AddCommGroup N] [Module Γ'' N] [Module k N] [IsScalarTower k Γ'' N]

def Intertwines (σ : Γ → Γ') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) : Prop :=
  ∀ (s : Γ) (x : A' ⊗[k] P), f (actR k A' s x) = actR k A' (σ s) (f x)

theorem Intertwines.comp {σ : Γ → Γ'} {σ' : Γ' → Γ''} {f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q}
    {g : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] N} (hf : Intertwines σ f) (hg : Intertwines σ' g) :
    Intertwines (σ' ∘ σ) (g ∘ₗ f) := fun s x => by
  simp [LinearMap.comp_apply, hf s x, hg (σ s)]

theorem Intertwines.id : Intertwines (_root_.id : Γ → Γ) (LinearMap.id : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P) :=
  fun _ _ => rfl

theorem Intertwines.symm {e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q} {σ : Γ ≃ Γ'}
    (he : Intertwines σ (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)) :
    Intertwines σ.symm (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P) := fun s y => by
  apply e.injective
  change e (e.symm (actR k A' s y)) = e (actR k A' (σ.symm s) (e.symm y))
  rw [LinearEquiv.apply_symm_apply]
  have := he (σ.symm s) (e.symm y)
  simp only [LinearEquiv.coe_coe, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem Intertwines.baseChange (σ : Γ → Γ') (r : P →ₗ[k] Q) (hr : ∀ (s : Γ) (m : P), r (s • m) = σ s • r m) :
    Intertwines σ (r.baseChange A') := fun s x => by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [hr]
  | add x y hx hy => simp only [map_add, hx, hy]

end Intertwines

section Ext

variable {k : Type*} [CommRing k] {Γ : Type*} [CommRing Γ] [Algebra k Γ]
  {A' : Type*} [CommRing A'] [Algebra k A']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {N : Type*} [AddCommGroup N] [Module A' N]

theorem linearMap_ext_of_span (F G : A' ⊗[k] P →ₗ[A'] N) (T : Γ → N → N)
    (hF : ∀ (s : Γ) (x : A' ⊗[k] P), F (actR k A' s x) = T s (F x))
    (hG : ∀ (s : Γ) (x : A' ⊗[k] P), G (actR k A' s x) = T s (G x))
    (gens : Set P) (hgens : Submodule.span Γ gens = ⊤)
    (h : ∀ m ∈ gens, F ((1 : A') ⊗ₜ[k] m) = G ((1 : A') ⊗ₜ[k] m)) : F = G := by

  let S : Submodule Γ P :=
    { carrier := {m | F ((1 : A') ⊗ₜ[k] m) = G ((1 : A') ⊗ₜ[k] m)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, tmul_add, map_add] at ha hb ⊢; rw [ha, hb]
      zero_mem' := by simp
      smul_mem' := fun s m hm => by
        simp only [Set.mem_setOf_eq] at hm ⊢
        rw [← actR_tmul k A', hF, hG, hm] }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← hgens, Submodule.span_le]; exact h
  have h1 : ∀ m : P, F ((1 : A') ⊗ₜ[k] m) = G ((1 : A') ⊗ₜ[k] m) := fun m => by
    have : m ∈ S := by rw [hS]; trivial
    exact this
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rw [tmul_eq_smul_one_tmul k A', map_smul, map_smul, h1]
  | add x y hx hy => simp only [map_add, hx, hy]

end Ext

section Push

variable {k : Type*} [CommRing k] {Γ Γ' : Type*} [CommRing Γ] [Algebra k Γ] [CommRing Γ'] [Algebra k Γ']
  {A' A'' : Type*} [CommRing A'] [Algebra k A'] [CommRing A''] [Algebra k A'']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {Q : Type*} [AddCommGroup Q] [Module Γ' Q] [Module k Q] [IsScalarTower k Γ' Q]
  {N : Type*} [AddCommGroup N] [Module k N]

private noncomputable def _root_.AlgebraicGeometry.RelPicard.LFP.push (h : A' →ₐ[k] A'') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) :
    A'' ⊗[k] P →ₗ[A''] A'' ⊗[k] Q :=
  LinearMap.liftBaseChange A''
    ((h.toLinearMap.rTensor Q) ∘ₗ (f.restrictScalars k) ∘ₗ (TensorProduct.mk k A' P 1))

p2m_export "AlgebraicGeometry.RelPicard.LFP" "push"
@[scoped simp] theorem push_tmul (h : A' →ₐ[k] A'') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (a : A'') (m : P) :
    push h f (a ⊗ₜ[k] m) = a • h.toLinearMap.rTensor Q (f ((1 : A') ⊗ₜ[k] m)) := by
  simp [push, LinearMap.liftBaseChange_tmul]

theorem push_rTensor (h : A' →ₐ[k] A'') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (x : A' ⊗[k] P) :
    push h f (h.toLinearMap.rTensor P x) = h.toLinearMap.rTensor Q (f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, push_tmul, ← rTensor_smul' k A' h,
      ← map_smul, ← tmul_eq_smul_one_tmul k A']
  | add x y hx hy => simp only [map_add, hx, hy]

theorem push_id (h : A' →ₐ[k] A'') :
    push h (LinearMap.id : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P) = LinearMap.id := by
  ext m; simp

theorem push_comp (h : A' →ₐ[k] A'') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)
    (g : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] N) :
    push h (g ∘ₗ f) = push h g ∘ₗ push h f := by
  ext m
  simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, push_tmul, one_smul]
  rw [push_rTensor]

theorem Intertwines.push {σ : Γ → Γ'} (h : A' →ₐ[k] A'') {f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q}
    (hf : Intertwines σ f) : Intertwines σ (push h f) := fun s x => by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [actR_tmul, push_tmul, push_tmul, ← actR_tmul k A', hf, rTensor_actR, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rTensor_baseChange (h : A' →ₐ[k] A'') {M M' : Type*} [AddCommGroup M] [Module k M] [AddCommGroup M']
    [Module k M'] (r : M →ₗ[k] M') (x : A' ⊗[k] M) :
    h.toLinearMap.rTensor M' (r.baseChange A' x) = r.baseChange A'' (h.toLinearMap.rTensor M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem push_square (h : A' →ₐ[k] A'') {P' : Type*} [AddCommGroup P'] [Module k P'] {Q' : Type*} [AddCommGroup Q']
    [Module k Q'] (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P') (g : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] Q')
    (r : P →ₗ[k] Q) (r' : P' →ₗ[k] Q') (hsq : ∀ x, g (r.baseChange A' x) = r'.baseChange A' (f x))
    (y : A'' ⊗[k] P) : push h g (r.baseChange A'' y) = r'.baseChange A'' (push h f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, push_tmul, push_tmul, map_smul, ← rTensor_baseChange, ← hsq,
      LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_span_range_of_algEquiv {Γ'' : Type*} [CommRing Γ''] [Algebra A' Γ'']
    (e : A' ⊗[k] Γ ≃ₐ[A'] Γ'') (φ : Γ → Γ'') (he : ∀ s, e ((1 : A') ⊗ₜ[k] s) = φ s) (y : Γ'') :
    y ∈ Submodule.span A' (Set.range φ) := by
  obtain ⟨x, rfl⟩ := e.surjective y
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul a s =>
    rw [tmul_eq_smul_one_tmul k A' a s, map_smul, he]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨s, rfl⟩)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

noncomputable def pushEquiv (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q) :
    A'' ⊗[k] P ≃ₗ[A''] A'' ⊗[k] Q :=
  LinearEquiv.ofLinear (push h (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q))
    (push h (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P))
    (by rw [← push_comp]; simp [push_id])
    (by rw [← push_comp]; simp [push_id])

@[scoped simp] theorem pushEquiv_apply (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q) (x : A'' ⊗[k] P) :
    pushEquiv h e x = push h (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) x := rfl

@[scoped simp] theorem pushEquiv_symm_apply (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q)
    (x : A'' ⊗[k] Q) :
    (pushEquiv h e).symm x = push h (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P) x := rfl

theorem coe_pushEquiv (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q) :
    (pushEquiv h e : A'' ⊗[k] P →ₗ[A''] A'' ⊗[k] Q) = push h (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) := rfl

end Push

section Orient

variable (k : Type*) [CommRing k] (Γ : Type*) [CommRing Γ] [Algebra k Γ]
  (A' : Type*) [CommRing A'] [Algebra k A']
  (P : Type*) [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]

noncomputable def orient : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[k] A' ⊗[k] P :=
  ((TensorProduct.comm Γ (Γ ⊗[k] A') P).restrictScalars k) ≪≫ₗ
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange k Γ Γ P A').restrictScalars k) ≪≫ₗ
  (TensorProduct.comm k P A')

@[scoped simp] theorem orient_tmul (γ : Γ) (a : A') (m : P) :
    orient k Γ A' P ((γ ⊗ₜ[k] a) ⊗ₜ[Γ] m) = a ⊗ₜ[k] (γ • m) := by
  simp [orient]

@[scoped simp] theorem orient_symm_tmul (a : A') (m : P) :
    (orient k Γ A' P).symm (a ⊗ₜ[k] m) = ((1 : Γ) ⊗ₜ[k] a) ⊗ₜ[Γ] m := by
  rw [LinearEquiv.symm_apply_eq, orient_tmul, one_smul]

theorem orient_smul (γ : Γ) (a : A') (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A' P ((γ ⊗ₜ[k] a) • x) = a • actR k A' γ (orient k Γ A' P x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul γ' a' =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, orient_tmul,
        orient_tmul, actR_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_smul]
    | add x y hx hy => simp only [smul_add, add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem orient_smul_left (a : A') (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A' P (((1 : Γ) ⊗ₜ[k] a) • x) = a • orient k Γ A' P x := by
  rw [orient_smul, actR_one, LinearMap.id_apply]

theorem orient_smul_right (γ : Γ) (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A' P ((γ ⊗ₜ[k] (1 : A')) • x) = actR k A' γ (orient k Γ A' P x) := by
  rw [orient_smul, one_smul]

theorem orient_symm_smul (a : A') (y : A' ⊗[k] P) :
    (orient k Γ A' P).symm (a • y) = ((1 : Γ) ⊗ₜ[k] a) • (orient k Γ A' P).symm y := by
  rw [LinearEquiv.symm_apply_eq, orient_smul_left, LinearEquiv.apply_symm_apply]

theorem orient_symm_actR (γ : Γ) (y : A' ⊗[k] P) :
    (orient k Γ A' P).symm (actR k A' γ y) = (γ ⊗ₜ[k] (1 : A')) • (orient k Γ A' P).symm y := by
  rw [LinearEquiv.symm_apply_eq, orient_smul_right, LinearEquiv.apply_symm_apply]

theorem orient_rTensor_map {A'' : Type*} [CommRing A''] [Algebra k A''] (h : A' →ₐ[k] A'')
    (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A'' P ((Algebra.TensorProduct.map (AlgHom.id Γ Γ) h).toLinearMap.rTensor P x) =
      h.toLinearMap.rTensor P (orient k Γ A' P x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul γ a => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {k Γ A' P}
variable {Q : Type*} [AddCommGroup Q] [Module Γ Q] [Module k Q] [IsScalarTower k Γ Q]

noncomputable def fromOrient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q where
  toFun y := orient k Γ A' Q (f ((orient k Γ A' P).symm y))
  map_add' y y' := by simp
  map_smul' a y := by
    rw [orient_symm_smul, map_smul, orient_smul_left, RingHom.id_apply]

theorem fromOrient_apply (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) (y : A' ⊗[k] P) :
    fromOrient f y = orient k Γ A' Q (f ((orient k Γ A' P).symm y)) := rfl

theorem fromOrient_orient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q)
    (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    fromOrient f (orient k Γ A' P x) = orient k Γ A' Q (f x) := by
  rw [fromOrient_apply, LinearEquiv.symm_apply_apply]

theorem intertwines_fromOrient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    Intertwines (_root_.id : Γ → Γ) (fromOrient f) := fun s y => by
  rw [fromOrient_apply, fromOrient_apply, orient_symm_actR, map_smul, orient_smul_right]; rfl

noncomputable def toOrient (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (hf : Intertwines (_root_.id : Γ → Γ) f) :
    (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q where
  toFun x := (orient k Γ A' Q).symm (f (orient k Γ A' P x))
  map_add' x x' := by simp
  map_smul' b x := by
    rw [RingHom.id_apply]
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul γ a =>
      rw [orient_smul, map_smul, hf, LinearEquiv.symm_apply_eq, orient_smul, LinearEquiv.apply_symm_apply]
      rfl
    | add b b' hb hb' => simp only [add_smul, map_add, hb, hb']

theorem toOrient_apply (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (hf : Intertwines (_root_.id : Γ → Γ) f)
    (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    toOrient f hf x = (orient k Γ A' Q).symm (f (orient k Γ A' P x)) := rfl

theorem fromOrient_toOrient (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (hf : Intertwines (_root_.id : Γ → Γ) f) :
    fromOrient (toOrient f hf) = f := by
  refine LinearMap.ext fun y => ?_
  rw [fromOrient_apply, toOrient_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem toOrient_fromOrient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    toOrient (fromOrient f) (intertwines_fromOrient f) = f := by
  refine LinearMap.ext fun x => ?_
  rw [toOrient_apply, fromOrient_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

noncomputable def fromOrientEquiv (e : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q :=
  LinearEquiv.ofLinear (fromOrient (e : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q))
    (fromOrient (e.symm : (Γ ⊗[k] A') ⊗[Γ] Q →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] P))
    (by refine LinearMap.ext fun y => ?_; simp [fromOrient_apply])
    (by refine LinearMap.ext fun y => ?_; simp [fromOrient_apply])

@[scoped simp] theorem coe_fromOrientEquiv (e : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    (fromOrientEquiv e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) =
      fromOrient (e : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) := rfl

theorem fromOrientEquiv_apply (e : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) (y : A' ⊗[k] P) :
    fromOrientEquiv e y = orient k Γ A' Q (e ((orient k Γ A' P).symm y)) := rfl

noncomputable def toOrientEquiv (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q)
    (he : Intertwines (_root_.id : Γ → Γ) (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)) :
    (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q :=
  LinearEquiv.ofLinear (toOrient (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) he)
    (toOrient (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P)
      (by simpa using (Intertwines.symm (σ := Equiv.refl Γ) he)))
    (by refine LinearMap.ext fun y => ?_; simp [toOrient_apply])
    (by refine LinearMap.ext fun y => ?_; simp [toOrient_apply])

theorem toOrientEquiv_apply (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q)
    (he : Intertwines (_root_.id : Γ → Γ) (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)) (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    toOrientEquiv e he x = (orient k Γ A' Q).symm (e (orient k Γ A' P x)) := rfl

end Orient

section FG

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  {N : Type*} [AddCommGroup N] [Module k N]

theorem exists_fg_le_forall_rTensor_inclusion_eq (D : Subalgebra k A) (hD : D.FG)
    {X : Type*} (S : Finset X) (t t' : X → ↥D ⊗[k] N)
    (h : ∀ x ∈ S, D.val.toLinearMap.rTensor N (t x) = D.val.toLinearMap.rTensor N (t' x)) :
    ∃ (D' : Subalgebra k A) (hDD' : D ≤ D'), D'.FG ∧
      ∀ x ∈ S, (Subalgebra.inclusion hDD').toLinearMap.rTensor N (t x) =
        (Subalgebra.inclusion hDD').toLinearMap.rTensor N (t' x) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨D, le_rfl, hD, fun x hx => (Finset.notMem_empty x hx).elim⟩
  | insert x₀ S hx₀ ih =>
    obtain ⟨D', hDD', hD', hS⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))

    have hval : D'.val.comp (Subalgebra.inclusion hDD') = D.val := by ext; rfl
    have h₀ : D'.val.toLinearMap.rTensor N ((Subalgebra.inclusion hDD').toLinearMap.rTensor N (t x₀)) =
        D'.val.toLinearMap.rTensor N ((Subalgebra.inclusion hDD').toLinearMap.rTensor N (t' x₀)) := by
      simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap, hval]
      exact h x₀ (Finset.mem_insert_self x₀ S)
    obtain ⟨D'', hD'D'', hD'', h₀'⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hD' h₀
    refine ⟨D'', hDD'.trans hD'D'', hD'', fun x hx => ?_⟩
    have hincl : (Subalgebra.inclusion hD'D'').comp (Subalgebra.inclusion hDD') =
        Subalgebra.inclusion (hDD'.trans hD'D'') := by ext; rfl
    rw [← hincl, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h₀'
    · rw [hS x hx]

end FG

end AlgebraicGeometry.RelPicard.LFP
end P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf
