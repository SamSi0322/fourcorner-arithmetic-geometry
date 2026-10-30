import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor

namespace FourCorner.RigidificationCompensation

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

def lbTB_tensorExchange {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V]
    (A B C D : V) : (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D) :=
  α_ A B (C ⊗ D) ≪≫ (Iso.refl A ⊗ᵢ ((α_ B C D).symm ≪≫ (β_ B C ⊗ᵢ Iso.refl D) ≪≫ α_ C B D)) ≪≫
    (α_ A C (B ⊗ D)).symm

theorem nonempty_rigidify_pullback_tensor_iso
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T)
    {N : T.Modules} (hN : Scheme.Modules.IsInvertible N)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q ((Scheme.Modules.pullback q).obj N ⊗ L) ≅
      Scheme.Modules.rigidify σ q L) := by
  have hσL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.IsInvertible.pullback σ hL
  obtain ⟨_, ⟨pairN⟩⟩ := Scheme.Modules.IsInvertible.dual hN
  obtain ⟨dt⟩ := Scheme.Modules.IsInvertible.dual_tensor hN hσL

  let eN : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback q).obj N) ≅ N :=
    (Scheme.Modules.pullbackComp σ q).app N ≪≫ (Scheme.Modules.pullbackCongr hσq).app N ≪≫
      (Scheme.Modules.pullbackId (X := T)).app N

  let eD : Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj
      ((Scheme.Modules.pullback q).obj N ⊗ L)) ≅
      Scheme.Modules.dual N ⊗ Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.dualMapIso (Scheme.Modules.pullbackTensorObjIso σ _ _ ≪≫ (eN ⊗ᵢ Iso.refl _)) ≪≫
      dt

  let eU : (Scheme.Modules.pullback q).obj N ⊗
      (Scheme.Modules.pullback q).obj (Scheme.Modules.dual N) ≅ 𝟙_ P.Modules :=
    (Scheme.Modules.pullbackTensorObjIso q N _).symm ≪≫ (Scheme.Modules.pullback q).mapIso pairN ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso q
  refine ⟨?_⟩
  change ((Scheme.Modules.pullback q).obj N ⊗ L) ⊗ (Scheme.Modules.pullback q).obj _ ≅
    L ⊗ (Scheme.Modules.pullback q).obj _
  exact (Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback q).mapIso eD ≪≫
      Scheme.Modules.pullbackTensorObjIso q _ _)) ≪≫
    lbTB_tensorExchange _ _ _ _ ≪≫ (eU ⊗ᵢ Iso.refl _) ≪≫ λ_ _


/-- The actual compensation isomorphism; its inverse is supplied by the constructed sheaf iso. -/
noncomputable def rigidifyPullbackTensorIso
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T)
    {N : T.Modules} (hN : Scheme.Modules.IsInvertible N)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.rigidify σ q ((Scheme.Modules.pullback q).obj N ⊗ L) ≅
      Scheme.Modules.rigidify σ q L :=
  (nonempty_rigidify_pullback_tensor_iso hσq hN hL).some

@[simp] theorem rigidifyPullbackTensorIso_hom_inv_id
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T)
    {N : T.Modules} (hN : Scheme.Modules.IsInvertible N)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    (rigidifyPullbackTensorIso hσq hN hL).hom ≫
      (rigidifyPullbackTensorIso hσq hN hL).inv = 𝟙 _ :=
  (rigidifyPullbackTensorIso hσq hN hL).hom_inv_id

@[simp] theorem rigidifyPullbackTensorIso_inv_hom_id
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T)
    {N : T.Modules} (hN : Scheme.Modules.IsInvertible N)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    (rigidifyPullbackTensorIso hσq hN hL).inv ≫
      (rigidifyPullbackTensorIso hσq hN hL).hom = 𝟙 _ :=
  (rigidifyPullbackTensorIso hσq hN hL).inv_hom_id

/-- Rigidification has a counit on a sheaf whose restriction along the section is trivial. -/
noncomputable def rigidifyCounitIso
    {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) {L : P.Modules}
    (e : (Scheme.Modules.pullback σ).obj L ≅ 𝟙_ T.Modules) :
    Scheme.Modules.rigidify σ q L ≅ L := by
  let d := Scheme.Modules.dualMapIso e
  let du : Scheme.Modules.dual (𝟙_ T.Modules) ≅ 𝟙_ T.Modules :=
    (λ_ _).symm ≪≫ (Scheme.Modules.isInvertible_unit T).dual.2.some
  exact (Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback q).mapIso (d ≪≫ du) ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso q)) ≪≫ ρ_ L

@[simp] theorem rigidifyCounitIso_hom_inv_id
    {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) {L : P.Modules}
    (e : (Scheme.Modules.pullback σ).obj L ≅ 𝟙_ T.Modules) :
    (rigidifyCounitIso σ q e).hom ≫ (rigidifyCounitIso σ q e).inv = 𝟙 _ :=
  (rigidifyCounitIso σ q e).hom_inv_id

@[simp] theorem rigidifyCounitIso_inv_hom_id
    {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) {L : P.Modules}
    (e : (Scheme.Modules.pullback σ).obj L ≅ 𝟙_ T.Modules) :
    (rigidifyCounitIso σ q e).inv ≫ (rigidifyCounitIso σ q e).hom = 𝟙 _ :=
  (rigidifyCounitIso σ q e).inv_hom_id

end FourCorner.RigidificationCompensation
