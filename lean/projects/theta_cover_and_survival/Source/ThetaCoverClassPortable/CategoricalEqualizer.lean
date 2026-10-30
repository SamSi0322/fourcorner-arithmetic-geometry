import ThetaCoverClassPortable.TensorCoordinates
import ThetaCoverClassPortable.CofacesDefinitions
import ThetaCoverClassPortable.TensorTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct CategoryTheory
open scoped ChangeOfRings

noncomputable section
namespace Module.FaithfullyFlat

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem transport_element {A T : Type u} [CommRing T]
    (F : A → ModuleCat.{u} T) (v : ∀ a, F a) {a b : A} (h : a = b) :
    (eqToHom (congrArg F h)) (v a) = v b := by
  cases h
  rfl

theorem eqToHom_extendScalars_tmul {T : Type u} [CommRing T]
    {f g : R →+* T} (h : f = g) (M : ModuleCat.{u} R) (t : T) (m : M) :
    (eqToHom (congrArg (fun f : R →+* T => (ModuleCat.extendScalars f).obj M) h))
      (t ⊗ₜ[R, f] m) = t ⊗ₜ[R, g] m := by
  exact transport_element (fun k : R →+* T => (ModuleCat.extendScalars k).obj M)
    (fun k => t ⊗ₜ[R, k] m) h

set_option maxHeartbeats 200000 in
theorem comparison_one_tmul {T : Type u} [CommRing T]
    (f : R →+* S) (g₁ g₂ : S →+* T) (h : g₁.comp f = g₂.comp f)
    (M : ModuleCat.{u} R) (m : M) :
    ((ModuleCat.extendScalarsComp f g₁).inv.app M ≫
      eqToHom (congrArg (fun k : R →+* T => (ModuleCat.extendScalars k).obj M) h) ≫
      (ModuleCat.extendScalarsComp f g₂).hom.app M)
      ((1 : T) ⊗ₜ[S, g₁] ((1 : S) ⊗ₜ[R, f] m)) =
        (1 : T) ⊗ₜ[S, g₂] ((1 : S) ⊗ₜ[R, f] m) := by
  let e := ModuleCat.extendScalarsComp f g₁
  have hh : e.hom.app M ((1 : T) ⊗ₜ[R, g₁.comp f] m) =
      (1 : T) ⊗ₜ[S, g₁] ((1 : S) ⊗ₜ[R, f] m) :=
    ModuleCat.extendScalarsComp_hom_app_one_tmul f g₁ M m
  have hi := congrArg (fun k => k ((1 : T) ⊗ₜ[R, g₁.comp f] m))
    (Iso.hom_inv_id_app e M)
  change e.inv.app M (e.hom.app M ((1 : T) ⊗ₜ[R, g₁.comp f] m)) =
    (1 : T) ⊗ₜ[R, g₁.comp f] m at hi
  erw [hh] at hi
  change (ModuleCat.extendScalarsComp f g₂).hom.app M
    ((eqToHom (congrArg (fun k : R →+* T => (ModuleCat.extendScalars k).obj M) h))
      (e.inv.app M _)) = _
  rw [hi, eqToHom_extendScalars_tmul R h M]
  exact ModuleCat.extendScalarsComp_hom_app_one_tmul f g₂ M m

theorem canonical_def (M : ModuleCat.{u} R) :
    Algebra.DescentCofaces.canonical R S M =
      (ModuleCat.extendScalarsComp (algebraMap R S) (Algebra.DescentCofaces.i₁ R S).hom).inv.app M ≫
        eqToHom (congrArg (fun k : R →+* S ⊗[R] S => (ModuleCat.extendScalars k).obj M)
          (Algebra.DescentCofaces.i₁_comp_algebraMap_eq R S)) ≫
        (ModuleCat.extendScalarsComp (algebraMap R S) (Algebra.DescentCofaces.i₂ R S).hom).hom.app M := rfl

theorem canonical_factor (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalarsComp (algebraMap R S) (Algebra.DescentCofaces.i₁ R S).hom).hom.app M ≫
      Algebra.DescentCofaces.canonical R S M =
        eqToHom (congrArg (fun k : R →+* S ⊗[R] S => (ModuleCat.extendScalars k).obj M)
          (Algebra.DescentCofaces.i₁_comp_algebraMap_eq R S)) ≫
        (ModuleCat.extendScalarsComp (algebraMap R S) (Algebra.DescentCofaces.i₂ R S).hom).hom.app M := by
  rw [canonical_def]
  simp only [← Category.assoc]
  erw [Iso.hom_inv_id_app]
  simp only [Category.id_comp]

theorem comp_hom_unit_explicit {T : Type u} [CommRing T]
    (f : R →+* S) (g : S →+* T) (M : ModuleCat.{u} R) (m : M) :
    (ModuleCat.extendScalarsComp f g).hom.app M ((1 : T) ⊗ₜ[R, g.comp f] m) =
      (1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m) :=
  ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m

theorem comp_inv_hom_explicit {T : Type u} [CommRing T]
    (f : R →+* S) (g : S →+* T) (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalarsComp f g).inv.app M ≫
      (ModuleCat.extendScalarsComp f g).hom.app M = 𝟙 _ :=
  Iso.inv_hom_id_app (ModuleCat.extendScalarsComp f g) M

theorem comp_hom_transport_unit {T : Type u} [CommRing T]
    (f : R →+* S) (g₁ g₂ : S →+* T) (h : g₁.comp f = g₂.comp f)
    (M : ModuleCat.{u} R) (m : M) :
    (ModuleCat.extendScalarsComp f g₂).hom.app M
      ((eqToHom (congrArg (fun k : R →+* T => (ModuleCat.extendScalars k).obj M) h))
        ((1 : T) ⊗ₜ[R, g₁.comp f] m)) =
      (1 : T) ⊗ₜ[S, g₂] ((1 : S) ⊗ₜ[R, f] m) :=
  (congrArg ((ModuleCat.extendScalarsComp f g₂).hom.app M)
    (eqToHom_extendScalars_tmul R h M 1 m)).trans (comp_hom_unit_explicit R S f g₂ M m)


def algebraMapRestricted :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
  { AddEquiv.refl S with
    map_smul' := by
      intro r s
      exact (Algebra.smul_def r (show S from s)).symm }

def extendedTensorEquiv (M : Type u) [AddCommGroup M] [Module R M] :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M) ≃ₗ[S] S ⊗[R] M := by
  let e := TensorProduct.congr (algebraMapRestricted R S) (LinearEquiv.refl R M)
  exact
  { e.toAddEquiv with
    map_smul' := by
      intro s x
      change e (s • x) = s • e x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a m => rfl
      | add x y hx hy => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hx hy }

@[simp] theorem extendedTensorEquiv_tmul (M : Type u) [AddCommGroup M] [Module R M]
    (s : S) (m : M) :
    extendedTensorEquiv R S M (s ⊗ₜ[R, algebraMap R S] m) = s ⊗ₜ[R] m := rfl

def moduleIsoOfIsBaseChange {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {f : M →ₗ[R] N} (h : IsBaseChange S f) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M) ≅ ModuleCat.of S N :=
  (extendedTensorEquiv R S M ≪≫ₗ h.equiv).toModuleIso

@[simp] theorem moduleIsoOfIsBaseChange_tmul {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {f : M →ₗ[R] N} (h : IsBaseChange S f) (s : S) (m : M) :
    (moduleIsoOfIsBaseChange R S h).hom (s ⊗ₜ[R, algebraMap R S] m) = s • f m := by
  change h.equiv (s ⊗ₜ[R] m) = _
  exact h.equiv_tmul s m

theorem square_of_fixed_generators {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (φ : (ModuleCat.extendScalars (leftInclusion R S)).obj (ModuleCat.of S N) ≅
      (ModuleCat.extendScalars (rightInclusion R S)).obj (ModuleCat.of S N))
    (can : (ModuleCat.extendScalars (leftInclusion R S)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)) ⟶
      (ModuleCat.extendScalars (rightInclusion R S)).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)))
    (hcan : ∀ m : M,
      can ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S] ((1 : S) ⊗ₜ[R, algebraMap R S] m)) =
        (1 : S ⊗[R] S) ⊗ₜ[S, rightInclusion R S] ((1 : S) ⊗ₜ[R, algebraMap R S] m))
    (hfixed : ∀ m, coactionOfIso R S N φ (f m) = (1 : S) ⊗ₜ[R] (f m)) :
    (ModuleCat.extendScalars (leftInclusion R S)).map (moduleIsoOfIsBaseChange R S hf).hom ≫ φ.hom =
      can ≫ (ModuleCat.extendScalars (rightInclusion R S)).map (moduleIsoOfIsBaseChange R S hf).hom := by
  let L := ((ModuleCat.extendScalars (leftInclusion R S)).map (moduleIsoOfIsBaseChange R S hf).hom ≫ φ.hom).hom
  let K := (can ≫ (ModuleCat.extendScalars (rightInclusion R S)).map (moduleIsoOfIsBaseChange R S hf).hom).hom
  have hunit (m : M) :
      L ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S] ((1 : S) ⊗ₜ[R, algebraMap R S] m)) =
      K ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S] ((1 : S) ⊗ₜ[R, algebraMap R S] m)) := by
    apply (rightCoordinates R S N).injective
    change rightCoordinates R S N (φ.hom _) = rightCoordinates R S N
      (((ModuleCat.extendScalars (rightInclusion R S)).map (moduleIsoOfIsBaseChange R S hf).hom) (can _))
    rw [hcan]
    change rightCoordinates R S N (φ.hom ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S]
      ((moduleIsoOfIsBaseChange R S hf).hom ((1 : S) ⊗ₜ[R, algebraMap R S] m)))) =
        rightCoordinates R S N ((1 : S ⊗[R] S) ⊗ₜ[S, rightInclusion R S]
          ((moduleIsoOfIsBaseChange R S hf).hom ((1 : S) ⊗ₜ[R, algebraMap R S] m)))
    rw [moduleIsoOfIsBaseChange_tmul, one_smul]
    change coactionOfIso R S N φ (f m) = rightCoordinates R S N
      ((1 : S ⊗[R] S) ⊗ₜ[S, rightInclusion R S] (f m))
    rw [hfixed, Algebra.TensorProduct.one_def, rightCoordinates_tmul, one_smul]
  have hall (x : (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)) :
      L ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S] x) =
      K ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S] x) := by
    induction x using TensorProduct.induction_on with
    | zero => rw [tmul_zero, L.map_zero, K.map_zero]
    | tmul s m =>
      have h : ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S] (s ⊗ₜ[R, algebraMap R S] m)) =
          (leftInclusion R S (show S from s)) • ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S]
            ((1 : S) ⊗ₜ[R, algebraMap R S] m)) := by
        have hu := ((ModuleCat.extendRestrictScalarsAdj (leftInclusion R S)).unit.app
          ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M))).hom.map_smul (show S from s)
          ((1 : S) ⊗ₜ[R, algebraMap R S] m)
        change (1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S]
          ((show S from s) • ((1 : S) ⊗ₜ[R, algebraMap R S] m)) =
            (leftInclusion R S (show S from s)) • ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S]
              ((1 : S) ⊗ₜ[R, algebraMap R S] m)) at hu
        have hs : (show S from s) • ((1 : S) ⊗ₜ[R, algebraMap R S] m) =
            s ⊗ₜ[R, algebraMap R S] m := by
          change ((show S from s) * (1 : S)) ⊗ₜ[R, algebraMap R S] m = _
          rw [mul_one]
        rw [hs] at hu
        exact hu
      rw [h, map_smul, map_smul, hunit]
    | add x y hx hy => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change L x = K x
  induction x using TensorProduct.induction_on with
  | zero => exact L.map_zero.trans K.map_zero.symm
  | tmul t x =>
    have h : (t ⊗ₜ[S, leftInclusion R S] x) =
        (show S ⊗[R] S from t) • ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S] x) := by
      change _ = ((show S ⊗[R] S from t) * (1 : S ⊗[R] S)) ⊗ₜ[S, leftInclusion R S] x
      rw [mul_one]
    change L _ = K _
    rw [h, map_smul, map_smul, hall]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option maxHeartbeats 300000 in
theorem square_of_fixed_elements_aux {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (φ : (ModuleCat.extendScalars (Algebra.DescentCofaces.i₁ R S).hom).obj (ModuleCat.of S N) ≅
      (ModuleCat.extendScalars (Algebra.DescentCofaces.i₂ R S).hom).obj (ModuleCat.of S N))
    (can : (ModuleCat.extendScalars (Algebra.DescentCofaces.i₁ R S).hom).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)) ⟶
      (ModuleCat.extendScalars (Algebra.DescentCofaces.i₂ R S).hom).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)))
    (aa : (ModuleCat.extendScalars ((Algebra.DescentCofaces.i₁ R S).hom.comp (algebraMap R S))).obj
        (ModuleCat.of R M) ⟶ (ModuleCat.extendScalars (Algebra.DescentCofaces.i₁ R S).hom).obj
          ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)))
    (ii : (ModuleCat.extendScalars (Algebra.DescentCofaces.i₁ R S).hom).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)) ⟶
      (ModuleCat.extendScalars ((Algebra.DescentCofaces.i₁ R S).hom.comp (algebraMap R S))).obj (ModuleCat.of R M))
    (bb : (ModuleCat.extendScalars ((Algebra.DescentCofaces.i₂ R S).hom.comp (algebraMap R S))).obj
        (ModuleCat.of R M) ⟶ (ModuleCat.extendScalars (Algebra.DescentCofaces.i₂ R S).hom).obj
          ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)))
    (c : (ModuleCat.extendScalars ((Algebra.DescentCofaces.i₁ R S).hom.comp (algebraMap R S))).obj
        (ModuleCat.of R M) ⟶
      (ModuleCat.extendScalars ((Algebra.DescentCofaces.i₂ R S).hom.comp (algebraMap R S))).obj (ModuleCat.of R M))
    (hInv : ii ≫ aa = 𝟙 _)
    (hfactor : aa ≫ can = c ≫ bb)
    (haunit : ∀ m : M, aa ((1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[R,
      (Algebra.DescentCofaces.i₁ R S).hom.comp (algebraMap R S)] m) =
      (1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[S, (Algebra.DescentCofaces.i₁ R S).hom]
        ((1 : S) ⊗ₜ[R, algebraMap R S] m))
    (hbunit : ∀ m : M, bb (c ((1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[R,
      (Algebra.DescentCofaces.i₁ R S).hom.comp (algebraMap R S)] m)) =
      (1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[S, (Algebra.DescentCofaces.i₂ R S).hom]
        ((1 : S) ⊗ₜ[R, algebraMap R S] m))
    (hfixed : ∀ m, coactionOfIso R S N φ (f m) = (1 : S) ⊗ₜ[R] (f m)) :
    (ModuleCat.extendScalars (Algebra.DescentCofaces.i₁ R S).hom).map
        (moduleIsoOfIsBaseChange R S hf).hom ≫ φ.hom =
      can ≫ (ModuleCat.extendScalars (Algebra.DescentCofaces.i₂ R S).hom).map
        (moduleIsoOfIsBaseChange R S hf).hom := by
  let θ := moduleIsoOfIsBaseChange R S hf
  letI : Epi aa := ⟨fun g h heq => by
    have hh := congrArg (fun q => ii ≫ q) heq
    simpa only [← Category.assoc, hInv, Category.id_comp] using hh⟩
  apply (cancel_epi aa).mp
  simp only [← Category.assoc]
  rw [hfactor]
  let L := ((aa ≫ (ModuleCat.extendScalars ((Algebra.DescentCofaces.i₁ R S).hom)).map θ.hom) ≫ φ.hom).hom
  let K := ((c ≫ bb) ≫ (ModuleCat.extendScalars ((Algebra.DescentCofaces.i₂ R S).hom)).map θ.hom).hom
  have hunit (m : M) :
      L ((1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[R, ((Algebra.DescentCofaces.i₁ R S).hom).comp (algebraMap R S)] m) =
      K ((1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[R, ((Algebra.DescentCofaces.i₁ R S).hom).comp (algebraMap R S)] m) := by
    let u := (1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[R, ((Algebra.DescentCofaces.i₁ R S).hom).comp (algebraMap R S)] m
    have ha := haunit m
    have hb := hbunit m
    apply (rightCoordinates R S N).injective
    change rightCoordinates R S N (φ.hom
      (((ModuleCat.extendScalars ((Algebra.DescentCofaces.i₁ R S).hom)).map θ.hom) (aa u))) =
        rightCoordinates R S N (((ModuleCat.extendScalars ((Algebra.DescentCofaces.i₂ R S).hom)).map θ.hom) (bb (c u)))
    rw [ha, hb]
    change rightCoordinates R S N (φ.hom ((1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[S, (Algebra.DescentCofaces.i₁ R S).hom]
      (θ.hom ((1 : S) ⊗ₜ[R, algebraMap R S] m)))) =
        rightCoordinates R S N ((1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[S, (Algebra.DescentCofaces.i₂ R S).hom]
          (θ.hom ((1 : S) ⊗ₜ[R, algebraMap R S] m)))
    rw [moduleIsoOfIsBaseChange_tmul, one_smul]
    change coactionOfIso R S N φ (f m) = _
    rw [hfixed, Algebra.TensorProduct.one_def, rightCoordinates_tmul, one_smul]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change L x = K x
  induction x using TensorProduct.induction_on with
  | zero => exact L.map_zero.trans K.map_zero.symm
  | tmul t m =>
    have h : t ⊗ₜ[R, ((Algebra.DescentCofaces.i₁ R S).hom).comp (algebraMap R S)] m =
        (show Algebra.DescentCofaces.R₂ R S from t) •
          ((1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[R, ((Algebra.DescentCofaces.i₁ R S).hom).comp (algebraMap R S)] m) := by
      change _ = ((show Algebra.DescentCofaces.R₂ R S from t) * (1 : Algebra.DescentCofaces.R₂ R S)) ⊗ₜ[R,
        ((Algebra.DescentCofaces.i₁ R S).hom).comp (algebraMap R S)] m
      rw [mul_one]
    rw [h, L.map_smul, K.map_smul, hunit]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy


set_option maxHeartbeats 300000 in
theorem square_of_fixed_elements {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    (φ : (ModuleCat.extendScalars ((Algebra.DescentCofaces.i₁ R S).hom)).obj (ModuleCat.of S N) ≅
      (ModuleCat.extendScalars ((Algebra.DescentCofaces.i₂ R S).hom)).obj (ModuleCat.of S N))
    (hfixed : ∀ m, coactionOfIso R S N φ (f m) = (1 : S) ⊗ₜ[R] (f m)) :
    (ModuleCat.extendScalars ((Algebra.DescentCofaces.i₁ R S).hom)).map (moduleIsoOfIsBaseChange R S hf).hom ≫ φ.hom =
      Algebra.DescentCofaces.canonical R S (ModuleCat.of R M) ≫
        (ModuleCat.extendScalars ((Algebra.DescentCofaces.i₂ R S).hom)).map (moduleIsoOfIsBaseChange R S hf).hom := by
  let M' := ModuleCat.of R M
  let a := (ModuleCat.extendScalarsComp (algebraMap R S) ((Algebra.DescentCofaces.i₁ R S).hom)).hom.app M'
  let b := (ModuleCat.extendScalarsComp (algebraMap R S) ((Algebra.DescentCofaces.i₂ R S).hom)).hom.app M'
  let c := tensorTransport (Algebra.DescentCofaces.i₁_comp_algebraMap_eq R S) M'

  let θ := moduleIsoOfIsBaseChange R S hf
  let aInv := (ModuleCat.extendScalarsComp (algebraMap R S) (Algebra.DescentCofaces.i₁ R S).hom).inv.app M'
  have hInv : aInv ≫ a = 𝟙 _ := comp_inv_hom_explicit R S (algebraMap R S) (Algebra.DescentCofaces.i₁ R S).hom M'
  have hfactor : a ≫ Algebra.DescentCofaces.canonical R S M' = c ≫ b :=
    (canonical_factor R S M').trans (congrArg (fun q => q ≫ b)
      (tensorTransport_eq_eqToHom (Algebra.DescentCofaces.i₁_comp_algebraMap_eq R S) M').symm)
  have haunit (m : M) : a ((1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[R,
      (Algebra.DescentCofaces.i₁ R S).hom.comp (algebraMap R S)] m) =
      (1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[S, (Algebra.DescentCofaces.i₁ R S).hom]
        ((1 : S) ⊗ₜ[R, algebraMap R S] m) :=
    comp_hom_unit_explicit R S (algebraMap R S) (Algebra.DescentCofaces.i₁ R S).hom M' m
  have hbunit (m : M) : b (c ((1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[R,
      (Algebra.DescentCofaces.i₁ R S).hom.comp (algebraMap R S)] m)) =
      (1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[S, (Algebra.DescentCofaces.i₂ R S).hom]
        ((1 : S) ⊗ₜ[R, algebraMap R S] m) :=
by
    have ht : c ((1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[R,
        (Algebra.DescentCofaces.i₁ R S).hom.comp (algebraMap R S)] m) =
        (1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[R,
          (Algebra.DescentCofaces.i₂ R S).hom.comp (algebraMap R S)] m :=
      tensorTransport_tmul (Algebra.DescentCofaces.i₁_comp_algebraMap_eq R S) M' 1 m
    have hu : b ((1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[R,
        (Algebra.DescentCofaces.i₂ R S).hom.comp (algebraMap R S)] m) =
        (1 : Algebra.DescentCofaces.R₂ R S) ⊗ₜ[S, (Algebra.DescentCofaces.i₂ R S).hom]
          ((1 : S) ⊗ₜ[R, algebraMap R S] m) :=
      comp_hom_unit_explicit R S (algebraMap R S) (Algebra.DescentCofaces.i₂ R S).hom M' m
    exact (congrArg b ht).trans hu


  exact square_of_fixed_elements_aux R S hf φ
    (Algebra.DescentCofaces.canonical R S M') a aInv b c hInv hfactor haunit hbunit hfixed

end Module.FaithfullyFlat
