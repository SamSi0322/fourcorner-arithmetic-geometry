import ThetaLocalSurvivalPortable.SquareZeroScalars
import Mathlib.RingTheory.Derivation.ToSquareZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped FourCorner.ThetaLocalSurvival.SquareZeroScalars
namespace FourCorner.ThetaLocalSurvival.Augmented

variable {A : Type} [CommRing A] [Algebra ℚ A]

/-- Standard restriction of scalars along the actual augmentation. -/
def AugModule (ε : A →ₐ[ℚ] ℚ) (M : Type) := M

instance (ε : A →ₐ[ℚ] ℚ) (M : Type) [AddCommGroup M] : AddCommGroup (AugModule ε M) :=
  inferInstanceAs (AddCommGroup M)
instance (ε : A →ₐ[ℚ] ℚ) (M : Type) [AddCommGroup M] [Module ℚ M] : Module ℚ (AugModule ε M) :=
  inferInstanceAs (Module ℚ M)
instance (ε : A →ₐ[ℚ] ℚ) (M : Type) [AddCommGroup M] [Module ℚ M] : Module A (AugModule ε M) :=
  Module.compHom M ε.toRingHom
instance (ε : A →ₐ[ℚ] ℚ) (M : Type) [AddCommGroup M] [Module ℚ M] :
    IsScalarTower ℚ A (AugModule ε M) := by
  constructor
  intro q a x
  change ε (q • a) • x=q • (ε a • x)
  rw [map_smul,smul_assoc]
instance (ε : A →ₐ[ℚ] ℚ) (M : Type) [AddCommGroup M] [Module ℚ M] :
    SMulCommClass ℚ A (AugModule ε M) := by
  constructor
  intro q a x
  change q • (ε a • x)=ε a • (q • x)
  exact smul_comm _ _ _

abbrev augDeriv (ε : A →ₐ[ℚ] ℚ) (M : Type) [AddCommGroup M] [Module ℚ M] :=
  Derivation ℚ A (AugModule ε M)

variable (ε : A →ₐ[ℚ] ℚ) {M N : Type} [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N]

def augMap (f : M →ₗ[ℚ] N) : AugModule ε M →ₗ[A] AugModule ε N where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := f.map_smul (ε a) x

def push (f : M →ₗ[ℚ] N) : augDeriv ε M →ₗ[ℚ] augDeriv ε N :=
  ((augMap ε f).compDer).restrictScalars ℚ

@[simp] theorem push_apply (f : M →ₗ[ℚ] N) (d : augDeriv ε M) (a : A) :
    push ε f d a=f (d a) := rfl

/-- Genuine augmented algebra maps to the actual trivial square-zero
extension; no group operation has been postulated on this subtype. -/
abbrev lifts := {f : A →ₐ[ℚ] TrivSqZeroExt ℚ M //
  (TrivSqZeroExt.fstHom ℚ ℚ M).comp f=ε}

def lift (d : augDeriv ε M) : A →ₐ[ℚ] TrivSqZeroExt ℚ M where
  toFun a := ⟨ε a,d a⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · exact ε.map_mul a b
    · change d (a*b)=ε a • d b+ε b • d a
      exact d.leibniz a b
  commutes' q := by
    ext
    · exact ε.commutes q
    · exact d.map_algebraMap q

@[simp] theorem lift_fst (d : augDeriv ε M) (a : A) : (lift ε d a).fst=ε a := rfl
@[simp] theorem lift_snd (d : augDeriv ε M) (a : A) : (lift ε d a).snd=d a := rfl

def unlift (f : lifts ε (M:=M)) : augDeriv ε M where
  toLinearMap :=
    { toFun a := (f.val a).snd
      map_add' a b := by change (f.val (a+b)).snd=(f.val a).snd+(f.val b).snd;rw [map_add];rfl
      map_smul' q a := by change (f.val (q • a)).snd=q • (f.val a).snd;rw [map_smul];rfl }
  map_one_eq_zero' := by change (f.val 1).snd=0;rw [map_one];rfl
  leibniz' a b := by
    have ha : (f.val a).fst=ε a := AlgHom.congr_fun f.property a
    have hb : (f.val b).fst=ε b := AlgHom.congr_fun f.property b
    change (f.val (a*b)).snd=ε a • (f.val b).snd+ε b • (f.val a).snd
    rw [map_mul,TrivSqZeroExt.snd_mul,ha,hb]
    rfl

def liftEquiv : augDeriv ε M ≃ lifts ε (M:=M) where
  toFun d := ⟨lift ε d,by ext; rfl⟩
  invFun := unlift ε
  left_inv d := by ext; rfl
  right_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · exact (AlgHom.congr_fun f.property a).symm
    · rfl

theorem lift_natural (f : M →ₗ[ℚ] N) (d : augDeriv ε M) :
    (TrivSqZeroExt.map f).comp (lift ε d)=lift ε (push ε f d) := by
  ext a <;> simp only [AlgHom.comp_apply,TrivSqZeroExt.fst_map,TrivSqZeroExt.snd_map,
    lift_fst,lift_snd,push_apply]

end FourCorner.ThetaLocalSurvival.Augmented
