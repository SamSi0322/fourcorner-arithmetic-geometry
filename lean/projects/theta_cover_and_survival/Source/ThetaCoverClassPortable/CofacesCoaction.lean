import ThetaCoverClassPortable.TensorCoordinates
import ThetaCoverClassPortable.CofacesDefinitions

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TensorProduct CategoryTheory
open scoped ChangeOfRings
noncomputable section
universe u
namespace Module.FaithfullyFlat
open Algebra.DescentCofaces
variable (R S N : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

abbrev j₃ : S →+* S ⊗[R] (S ⊗[R] S) := ((i₂ R S) ≫ c₂₃ R S).hom

def tripleEval : (S ⊗[R] (S ⊗[R] S)) →ₗ[R] N →ₗ[R] S ⊗[R] (S ⊗[R] N) :=
  TensorProduct.lift <| LinearMap.mk₂ R
    (fun a t => (TensorProduct.mk R S (S ⊗[R] N) a).comp <|
      (TensorProduct.lift (LinearMap.mk₂ R
        (fun b c => (TensorProduct.mk R S N b).comp ((DistribSMul.toLinearMap R N c)))
        (by intros; ext; simp [add_tmul]) (by intros; ext; simp [smul_tmul'])
        (by intros; ext; simp [add_smul, tmul_add]) (by intros; ext; simp [smul_assoc])) t))
    (by intros; ext; simp [add_tmul]) (by intros; ext; simp [smul_tmul'])
    (by intros; ext; simp [tmul_add]) (by intros; ext; simp)

@[simp] theorem tripleEval_tmul (a b c : S) (n : N) :
    tripleEval R S N (a ⊗ₜ[R] (b ⊗ₜ[R] c)) n = a ⊗ₜ[R] (b ⊗ₜ[R] (c • n)) := rfl

theorem tripleEval_balance (s : S) (q : S ⊗[R] (S ⊗[R] S)) (n : N) :
    tripleEval R S N ((j₃ R S s) * q) n = tripleEval R S N q (s • n) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      change tripleEval R S N ((1 ⊗ₜ[R] (1 ⊗ₜ[R] s)) * (a ⊗ₜ[R] (b ⊗ₜ[R] c))) n = _
      simp [Algebra.TensorProduct.tmul_mul_tmul, mul_smul, mul_comm s c]
    | add t u ht hu => simpa [tmul_add, mul_add] using congrArg₂ (· + ·) ht hu
  | add q t hq ht => simpa [mul_add] using congrArg₂ (· + ·) hq ht

def tripleCoordinates :
    ((ModuleCat.extendScalars (j₃ R S)).obj (ModuleCat.of S N)) →+
      S ⊗[R] (S ⊗[R] N) :=
  TensorProduct.liftAddHom
    { toFun := fun q => (tripleEval R S N q).toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
    (fun s q n => tripleEval_balance R S N s q n)

@[simp] theorem tripleCoordinates_tmul (a b c : S) (n : N) :
    tripleCoordinates R S N ((a ⊗ₜ[R] (b ⊗ₜ[R] c)) ⊗ₜ[S, j₃ R S] n) =
      a ⊗ₜ[R] (b ⊗ₜ[R] (c • n)) := rfl

variable {R S N}

def push (N : ModuleCat.{u} S) (i : S →+* S ⊗[R] S)
    (c : R₂ R S ⟶ R₃ R S) :
    ((ModuleCat.extendScalars i).obj N) →+
      ((ModuleCat.extendScalars (c.hom.comp i)).obj N) :=
  ((ModuleCat.extendScalarsComp i c.hom).inv.app N).hom.toAddMonoidHom.comp
    (((ModuleCat.extendRestrictScalarsAdj c.hom).unit.app _).hom.toAddMonoidHom)

@[simp] theorem push_tmul (N : ModuleCat.{u} S) (i : S →+* S ⊗[R] S)
    (c : R₂ R S ⟶ R₃ R S) (t : S ⊗[R] S) (n : N) :
    push N i c (t ⊗ₜ[S, i] n) = c.hom t ⊗ₜ[S, c.hom.comp i] n := by
  have h := ModuleCat.extendScalarsComp_hom_app_one_tmul i c.hom N n
  have h' := congrArg ((ModuleCat.extendScalarsComp i c.hom).inv.app N) h
  have hh : push N i c ((1 : S ⊗[R] S) ⊗ₜ[S, i] n) =
      (1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S, c.hom.comp i] n := by
    have hid := congrArg (fun f => f ((1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S, c.hom.comp i] n))
      (Iso.hom_inv_id_app (ModuleCat.extendScalarsComp i c.hom) N)
    change _ = (1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S, c.hom.comp i] n at hid
    exact h'.symm.trans hid
  have hs : ∀ (x : (ModuleCat.extendScalars i).obj N),
      push N i c (t • x) = c.hom t • push N i c x := by
    intro x
    change ((ModuleCat.extendScalarsComp i c.hom).inv.app N)
      ((1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S ⊗[R] S, c.hom] (t • x)) = _
    rw [← TensorProduct.smul_tmul]
    change ((ModuleCat.extendScalarsComp i c.hom).inv.app N)
      ((c.hom t * 1) ⊗ₜ[S ⊗[R] S, c.hom] x) = _
    rw [mul_one]
    have hm := ((ModuleCat.extendScalarsComp i c.hom).inv.app N).hom.map_smul
      (c.hom t) ((1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S ⊗[R] S, c.hom] x)
    erw [TensorProduct.smul_tmul'] at hm
    change ((ModuleCat.extendScalarsComp i c.hom).inv.app N)
      ((c.hom t * 1) ⊗ₜ[S ⊗[R] S, c.hom] x) = c.hom t • push N i c x at hm
    simpa only [mul_one] using hm
  have ht : t ⊗ₜ[S, i] n = t • ((1 : S ⊗[R] S) ⊗ₜ[S, i] n) := by
    change t ⊗ₜ[S, i] n = (t * 1) ⊗ₜ[S, i] n
    rw [mul_one]
  rw [ht, hs, hh]
  change (c.hom t * 1) ⊗ₜ[S, c.hom.comp i] n = _
  rw [mul_one]

@[simp] theorem push_zero (N : ModuleCat.{u} S) (i : S →+* S ⊗[R] S)
    (c : R₂ R S ⟶ R₃ R S) : push N i c 0 = 0 := (push N i c).map_zero
@[simp] theorem push_add (N : ModuleCat.{u} S) (i : S →+* S ⊗[R] S)
    (c : R₂ R S ⟶ R₃ R S) (x y : (ModuleCat.extendScalars i).obj N) :
    push N i c (x + y) = push N i c x + push N i c y := (push N i c).map_add x y

theorem T_push (N : ModuleCat.{u} S) (c : R₂ R S ⟶ R₃ R S)
    (φ : (ModuleCat.extendScalars (i₁ R S).hom).obj N ⟶
      (ModuleCat.extendScalars (i₂ R S).hom).obj N)
    (x : (ModuleCat.extendScalars (i₁ R S).hom).obj N) :
    T N c φ (push N (i₁ R S).hom c x) = push N (i₂ R S).hom c (φ x) := by
  change ((ModuleCat.extendScalarsComp (i₂ R S).hom c.hom).inv.app N)
    (((ModuleCat.extendScalars c.hom).map φ)
      (((ModuleCat.extendScalarsComp (i₁ R S).hom c.hom).hom.app N)
        (((ModuleCat.extendScalarsComp (i₁ R S).hom c.hom).inv.app N)
          ((1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S ⊗[R] S, c.hom] x)))) = _
  have hi := congrArg (fun f => f ((1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S ⊗[R] S, c.hom] x))
    (Iso.inv_hom_id_app (ModuleCat.extendScalarsComp (i₁ R S).hom c.hom) N)
  change ((ModuleCat.extendScalarsComp (i₁ R S).hom c.hom).hom.app N)
    (((ModuleCat.extendScalarsComp (i₁ R S).hom c.hom).inv.app N)
      ((1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S ⊗[R] S, c.hom] x)) =
      (1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S ⊗[R] S, c.hom] x at hi
  erw [hi]
  rfl

theorem T_unit (N : ModuleCat.{u} S) (c : R₂ R S ⟶ R₃ R S)
    (φ : (ModuleCat.extendScalars (i₁ R S).hom).obj N ⟶
      (ModuleCat.extendScalars (i₂ R S).hom).obj N) (n : N) :
    T N c φ ((1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S, c.hom.comp (i₁ R S).hom] n) =
      push N (i₂ R S).hom c (φ ((1 : S ⊗[R] S) ⊗ₜ[S, (i₁ R S).hom] n)) := by
  change ((ModuleCat.extendScalarsComp (i₂ R S).hom c.hom).inv.app N)
    (((ModuleCat.extendScalars c.hom).map φ)
      (((ModuleCat.extendScalarsComp (i₁ R S).hom c.hom).hom.app N)
        ((1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S, c.hom.comp (i₁ R S).hom] n))) = _
  rw [ModuleCat.extendScalarsComp_hom_app_one_tmul]
  rfl

variable (R S N)
theorem triple_push13 (x : (ModuleCat.extendScalars (rightInclusion R S)).obj (ModuleCat.of S N)) :
    tripleCoordinates R S N (push (ModuleCat.of S N) (rightInclusion R S) (c₁₃ R S) x) =
      (TensorProduct.mk R S N 1).lTensor S (rightCoordinates R S N x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [push_zero, map_zero, smul_zero, tmul_zero, zero_tmul]
  | tmul t n =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [push_zero, map_zero, smul_zero, tmul_zero, zero_tmul]
    | tmul a b =>
      erw [push_tmul, c₁₃_tmul, tripleCoordinates_tmul]
    | add t u ht hu => simpa only [add_tmul, push_add, map_add] using congrArg₂ (· + ·) ht hu
  | add x y hx hy => simpa only [push_add, map_add] using congrArg₂ (· + ·) hx hy

theorem triple_push23_smul (a b : S)
    (x : (ModuleCat.extendScalars (rightInclusion R S)).obj (ModuleCat.of S N)) :
    tripleCoordinates R S N ((a ⊗ₜ[R] (b ⊗ₜ[R] (1 : S))) •
      push (ModuleCat.of S N) (rightInclusion R S) (c₂₃ R S) x) =
        a ⊗ₜ[R] (b • rightCoordinates R S N x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [push_zero, map_zero, smul_zero, tmul_zero, zero_tmul]
  | tmul t n =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [push_zero, map_zero, smul_zero, tmul_zero, zero_tmul]
    | tmul c d =>
      erw [push_tmul]
      change tripleCoordinates R S N
        (((a ⊗ₜ[R] (b ⊗ₜ[R] (1 : S))) * (1 ⊗ₜ[R] (c ⊗ₜ[R] d))) ⊗ₜ[S, j₃ R S] n) = _
      erw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      simp only [mul_one, one_mul]
      erw [tripleCoordinates_tmul, rightCoordinates_tmul, smul_tmul']
      rfl
    | add t u ht hu => simpa only [add_tmul, push_add, map_add, smul_add, tmul_add] using congrArg₂ (· + ·) ht hu
  | add x y hx hy => simpa only [push_add, map_add, smul_add, tmul_add] using congrArg₂ (· + ·) hx hy


theorem triple_T23_push12
    (φ : (ModuleCat.extendScalars (leftInclusion R S)).obj (ModuleCat.of S N) ≅
      (ModuleCat.extendScalars (rightInclusion R S)).obj (ModuleCat.of S N))
    (x : (ModuleCat.extendScalars (rightInclusion R S)).obj (ModuleCat.of S N)) :
    tripleCoordinates R S N (T (ModuleCat.of S N) (c₂₃ R S) φ.hom
      (push (ModuleCat.of S N) (rightInclusion R S) (c₁₂ R S) x)) =
    ((coactionOfIso R S N φ).restrictScalars R).lTensor S (rightCoordinates R S N x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [push_zero, map_zero, zero_tmul]
  | tmul t n =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [push_zero, map_zero, zero_tmul]
    | tmul a b =>
      rw [push_tmul]
      have ht : (c₁₂ R S).hom (a ⊗ₜ[R] b) ⊗ₜ[S, (c₁₂ R S).hom.comp (i₂ R S).hom] n =
        (a ⊗ₜ[R] (b ⊗ₜ[R] (1 : S))) •
          ((1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S, (c₂₃ R S).hom.comp (i₁ R S).hom] n) := by
        change _ = ((a ⊗ₜ[R] (b ⊗ₜ[R] (1 : S))) * 1) ⊗ₜ[S, (c₂₃ R S).hom.comp (i₁ R S).hom] n
        rw [mul_one]
        rfl
      rw [ht, map_smul, T_unit]
      erw [triple_push23_smul]
      exact congrArg (fun z : S ⊗[R] N => a ⊗ₜ[R] z)
        ((coactionOfIso R S N φ).map_smul b n).symm
    | add t u ht hu => simpa only [add_tmul, push_add, map_add] using congrArg₂ (· + ·) ht hu
  | add x y hx hy => simpa only [push_add, map_add] using congrArg₂ (· + ·) hx hy

theorem coactionOfIso_coassoc_of_cocycle
    (φ : (ModuleCat.extendScalars (leftInclusion R S)).obj (ModuleCat.of S N) ≅
      (ModuleCat.extendScalars (rightInclusion R S)).obj (ModuleCat.of S N))
    (hcoc : Cocycle (ModuleCat.of S N) φ.hom) (n : N) :
    ((coactionOfIso R S N φ).restrictScalars R).lTensor S (coactionOfIso R S N φ n) =
      (TensorProduct.mk R S N 1).lTensor S (coactionOfIso R S N φ n) := by
  have h := congrArg (fun f => f ((1 : S ⊗[R] (S ⊗[R] S)) ⊗ₜ[S, (c₁₂ R S).hom.comp (i₁ R S).hom] n)) hcoc
  change T (ModuleCat.of S N) (c₂₃ R S) φ.hom
    (T (ModuleCat.of S N) (c₁₂ R S) φ.hom _) =
      T (ModuleCat.of S N) (c₁₃ R S) φ.hom _ at h
  rw [T_unit, T_unit] at h
  have hh := congrArg (tripleCoordinates R S N) h
  erw [triple_T23_push12, triple_push13] at hh
  exact hh

end Module.FaithfullyFlat
