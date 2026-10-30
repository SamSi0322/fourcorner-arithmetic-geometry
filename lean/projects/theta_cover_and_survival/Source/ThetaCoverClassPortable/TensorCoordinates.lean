import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import ThetaCoverClassPortable.CoactionEqualizer
import ThetaCoverClassPortable.CoactionAuxiliary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open TensorProduct

noncomputable section

namespace Module.FaithfullyFlat

universe u
variable (R S N : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

abbrev rightInclusion : S →+* S ⊗[R] S :=
  (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toRingHom

/-- Switching the factors turns restriction along the right inclusion into
restriction along the left inclusion. -/
def swapRestricted :
    (ModuleCat.restrictScalars (rightInclusion R S)).obj
      (ModuleCat.of (S ⊗[R] S) (S ⊗[R] S)) ≃ₗ[S] S ⊗[R] S :=
  { (Algebra.TensorProduct.comm R S S).toAddEquiv with
    map_smul' := by
      intro s t
      change (Algebra.TensorProduct.comm R S S)
        (((1 : S) ⊗ₜ[R] s) * (show S ⊗[R] S from t)) =
          s • (Algebra.TensorProduct.comm R S S) (show S ⊗[R] S from t)
      rw [map_mul]
      simp [Algebra.smul_def] }

def rightCoordinates :
    (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.restrictScalars (rightInclusion R S)).obj
        ((ModuleCat.extendScalars (rightInclusion R S)).obj (ModuleCat.of S N))) ≃ₗ[R]
          S ⊗[R] N := by
  let U := (ModuleCat.restrictScalars (rightInclusion R S)).obj
    (ModuleCat.of (S ⊗[R] S) (S ⊗[R] S))
  letI : Module R U := Module.compHom U (algebraMap R S)
  letI : IsScalarTower R S U := IsScalarTower.of_compHom R S U
  exact
  ((TensorProduct.congr (swapRestricted R S) (LinearEquiv.refl S N)) ≪≫ₗ
    TensorProduct.comm S (S ⊗[R] S) N).restrictScalars R ≪≫ₗ
  (AlgebraTensorModule.assoc R S S N S S).symm.restrictScalars R ≪≫ₗ
  ((TensorProduct.rid S N).restrictScalars R).rTensor S ≪≫ₗ
  TensorProduct.comm R N S

open scoped ChangeOfRings
@[simp] theorem rightCoordinates_tmul (s t : S) (n : N) :
    rightCoordinates R S N ((s ⊗ₜ[R] t) ⊗ₜ[S, rightInclusion R S] n) =
      s ⊗ₜ[R] (t • n) := by
  rfl

abbrev leftInclusion : S →+* S ⊗[R] S :=
  Algebra.TensorProduct.includeLeftRingHom

def leftRestricted :
    (ModuleCat.restrictScalars (leftInclusion R S)).obj
      (ModuleCat.of (S ⊗[R] S) (S ⊗[R] S)) ≃ₗ[S] S ⊗[R] S :=
  { AddEquiv.refl (S ⊗[R] S) with
    map_smul' := by
      intro s t
      change ((s ⊗ₜ[R] (1 : S)) * (show S ⊗[R] S from t)) = s • (show S ⊗[R] S from t)
      rw [Algebra.smul_def]
      rfl }

def leftCoordinates :
    (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.restrictScalars (leftInclusion R S)).obj
        ((ModuleCat.extendScalars (leftInclusion R S)).obj (ModuleCat.of S N))) ≃ₗ[R]
          S ⊗[R] N := by
  let U := (ModuleCat.restrictScalars (leftInclusion R S)).obj
    (ModuleCat.of (S ⊗[R] S) (S ⊗[R] S))
  letI : Module R U := Module.compHom U (algebraMap R S)
  letI : IsScalarTower R S U := IsScalarTower.of_compHom R S U
  exact
  ((TensorProduct.congr (leftRestricted R S) (LinearEquiv.refl S N)) ≪≫ₗ
    TensorProduct.comm S (S ⊗[R] S) N).restrictScalars R ≪≫ₗ
  (AlgebraTensorModule.assoc R S S N S S).symm.restrictScalars R ≪≫ₗ
  ((TensorProduct.rid S N).restrictScalars R).rTensor S ≪≫ₗ
  TensorProduct.comm R N S

@[simp] theorem leftCoordinates_tmul (s t : S) (n : N) :
    leftCoordinates R S N ((s ⊗ₜ[R] t) ⊗ₜ[S, leftInclusion R S] n) =
      t ⊗ₜ[R] (s • n) := by
  rfl

theorem rightCoordinates_left_smul (s : S)
    (x : (ModuleCat.extendScalars (rightInclusion R S)).obj (ModuleCat.of S N)) :
    rightCoordinates R S N ((leftInclusion R S s) • x) =
      s • rightCoordinates R S N x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t n =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      change rightCoordinates R S N ((((s ⊗ₜ[R] (1 : S)) * (a ⊗ₜ[R] b))) ⊗ₜ[S, rightInclusion R S] n) =
        s • rightCoordinates R S N ((a ⊗ₜ[R] b) ⊗ₜ[S, rightInclusion R S] n)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [rightCoordinates_tmul, rightCoordinates_tmul, smul_tmul']
      rfl
    | add a b ha hb => simpa only [add_tmul, smul_add, map_add] using congrArg₂ (· + ·) ha hb
  | add a b ha hb => simpa only [smul_add, map_add] using congrArg₂ (· + ·) ha hb

/-- The actual coaction induced by an isomorphism between the two pullbacks. -/
def coactionOfIso
    (φ : (ModuleCat.extendScalars (leftInclusion R S)).obj (ModuleCat.of S N) ≅
      (ModuleCat.extendScalars (rightInclusion R S)).obj (ModuleCat.of S N)) :
    N →ₗ[S] S ⊗[R] N where
  toFun n := rightCoordinates R S N (φ.hom ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S] n))
  map_add' n m := by
    rw [tmul_add, map_add, map_add]
  map_smul' s n := by
    have h : ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S] (s • n)) =
        (leftInclusion R S s) • ((1 : S ⊗[R] S) ⊗ₜ[S, leftInclusion R S] n) := by
      exact ((ModuleCat.extendRestrictScalarsAdj (leftInclusion R S)).unit.app
        (ModuleCat.of S N)).hom.map_smul s n
    rw [h, map_smul, rightCoordinates_left_smul]
    rfl

theorem coactionOfIso_injective [Module.FaithfullyFlat R S]
    (φ : (ModuleCat.extendScalars (leftInclusion R S)).obj (ModuleCat.of S N) ≅
      (ModuleCat.extendScalars (rightInclusion R S)).obj (ModuleCat.of S N)) :
    Function.Injective (coactionOfIso R S N φ) := by
  intro n m h
  change rightCoordinates R S N (φ.hom _) = rightCoordinates R S N (φ.hom _) at h
  have h' := φ.toLinearEquiv.injective ((rightCoordinates R S N).injective h)
  have h'' := congrArg (leftCoordinates R S N) h'
  apply tensorUnit_injective (R := R) (S := S)
  simp only [Algebra.TensorProduct.one_def] at h''
  change (1 : S) ⊗ₜ[R] ((1 : S) • n) = (1 : S) ⊗ₜ[R] ((1 : S) • m) at h''
  simpa only [one_smul, TensorProduct.mk_apply] using h''

theorem isBaseChange_ofIso_of_coassoc [Module.FaithfullyFlat R S]
    (φ : (ModuleCat.extendScalars (leftInclusion R S)).obj (ModuleCat.of S N) ≅
      (ModuleCat.extendScalars (rightInclusion R S)).obj (ModuleCat.of S N))
    (hcoassoc : ∀ n,
      ((coactionOfIso R S N φ).restrictScalars R).lTensor S (coactionOfIso R S N φ n) =
        (TensorProduct.mk R S N 1).lTensor S (coactionOfIso R S N φ n)) :
    IsBaseChange S (coactionInvariants (coactionOfIso R S N φ)).subtype :=
  isBaseChange_coactionInvariants _
    (counit_of_coassoc_of_injective _ (coactionOfIso_injective R S N φ) hcoassoc) hcoassoc

end Module.FaithfullyFlat
