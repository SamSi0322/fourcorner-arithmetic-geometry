import ThetaCoverClassPortable.AugmentedDerivations
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped FourCorner.ThetaLocalSurvival.SquareZeroScalars
namespace FourCorner.ThetaLocalSurvival.Augmented
variable {A : Type} [CommRing A] [Algebra ℚ A] (ε : A →ₐ[ℚ] ℚ)
variable (R : Type) [CommRing R] [Algebra ℚ R] (I : Ideal R) (hI : I^2=⊥)

def augOut {M : Type} (x : AugModule ε M) : M := x
@[simp] theorem augOut_zero {M : Type} [AddCommGroup M] : augOut ε (0 : AugModule ε M)=0 := rfl
@[simp] theorem augOut_add {M : Type} [AddCommGroup M] (x y : AugModule ε M) :
    augOut ε (x+y)=augOut ε x+augOut ε y := rfl
@[simp] theorem augOut_ascalar {M : Type} [AddCommGroup M] [Module ℚ M]
    (a : A) (x : AugModule ε M) : augOut ε (a • x)=ε a • augOut ε x := rfl

abbrev idealLifts := {f : A →ₐ[ℚ] R //
  (Ideal.Quotient.mkₐ ℚ I).comp f=(Algebra.ofId ℚ (R⧸I)).comp ε}

include hI in
theorem ideal_mul_zero (x y : I) : (x:R)*(y:R)=0 := by
  have h := Ideal.mul_mem_mul x.property y.property
  rw [←pow_two,hI] at h
  exact h

def idealLift (d : augDeriv ε I) : A →ₐ[ℚ] R where
  toFun a := algebraMap ℚ R (ε a)+(augOut ε (M:=I) (d a):R)
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := by simp only [map_add,augOut_add,Submodule.coe_add];ring
  map_mul' a b := by
    have hd : (augOut ε (M:=I) (d (a*b)):R)=algebraMap ℚ R (ε a)*(augOut ε (M:=I) (d b):R)+algebraMap ℚ R (ε b)*(augOut ε (M:=I) (d a):R) := by
      have h := congrArg (augOut ε (M:=I)) (d.leibniz a b)
      simp only [augOut_add,augOut_ascalar] at h
      have h' := congrArg (fun z : I => (z:R)) h
      simpa only [Submodule.coe_add,Submodule.coe_smul_of_tower,Algebra.smul_def] using h'
    simp only [map_mul,hd]
    have hz := ideal_mul_zero R I hI (augOut ε (M:=I) (d a)) (augOut ε (M:=I) (d b))
    linear_combination -hz
  commutes' q := by
    simp only [AlgHom.commutes,Derivation.map_algebraMap,augOut_zero,Submodule.coe_zero,add_zero]
    rfl

def idealUnlift (f : idealLifts ε R I) : augDeriv ε I := by
  let f0 : A →ₐ[ℚ] R := (Algebra.ofId ℚ R).comp ε
  have hf : (Ideal.Quotient.mkₐ ℚ I).comp f.val=(Ideal.Quotient.mkₐ ℚ I).comp f0 := by
    rw [f.property]
    ext a
    simp [f0]
  let d := diffToIdealOfQuotientCompEq I f.val f0 hf
  refine { toLinearMap := d, map_one_eq_zero' := ?_, leibniz' := ?_ }
  · apply Subtype.ext
    change f.val 1-algebraMap ℚ R (ε 1)=0
    simp
  · intro a b
    change (d (a*b):I)=ε a • (d b:I)+ε b • (d a:I)
    apply Subtype.ext
    simp only [Submodule.coe_add,Submodule.coe_smul_of_tower,Algebra.smul_def]
    change f.val (a*b)-algebraMap ℚ R (ε (a*b))=
      algebraMap ℚ R (ε a)*(f.val b-algebraMap ℚ R (ε b))+
        algebraMap ℚ R (ε b)*(f.val a-algebraMap ℚ R (ε a))
    have hz := ideal_mul_zero R I hI (augOut ε (M:=I) (d a)) (augOut ε (M:=I) (d b))
    change (f.val a-algebraMap ℚ R (ε a))*(f.val b-algebraMap ℚ R (ε b))=0 at hz
    simp only [map_mul]
    linear_combination hz

@[simp] theorem idealUnlift_coe (f : idealLifts ε R I) (a : A) :
    (augOut ε (M:=I) (idealUnlift ε R I hI f a):R)=f.val a-algebraMap ℚ R (ε a) := rfl
@[simp] theorem idealLift_apply (d : augDeriv ε I) (a : A) :
    idealLift ε R I hI d a=algebraMap ℚ R (ε a)+(augOut ε (M:=I) (d a):R) := rfl

def idealLiftEquiv : augDeriv ε I ≃ idealLifts ε R I where
  toFun d := ⟨idealLift ε R I hI d,by
    ext a
    change Ideal.Quotient.mk I (algebraMap ℚ R (ε a)+(augOut ε (M:=I) (d a):R))=algebraMap ℚ (R⧸I) (ε a)
    rw [map_add,Ideal.Quotient.eq_zero_iff_mem.mpr (augOut ε (M:=I) (d a)).property,add_zero]
    exact (Ideal.Quotient.mkₐ ℚ I).commutes (ε a)⟩
  invFun := idealUnlift ε R I hI
  left_inv d := by
    apply Derivation.ext
    intro a
    apply Subtype.ext
    change (augOut ε (M:=I) (idealUnlift ε R I hI _ a):R)=(augOut ε (M:=I) (d a):R)
    rw [idealUnlift_coe,idealLift_apply]
    exact add_sub_cancel_left _ _
  right_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    rw [idealLift_apply,idealUnlift_coe]
    ring

/-- The canonical map from the actual split square-zero extension into
an arbitrary genuine square-zero thickening. -/
def squareZeroToRing : TrivSqZeroExt ℚ I →ₐ[ℚ] R :=
  TrivSqZeroExt.lift (Algebra.ofId ℚ R) (I.subtype.restrictScalars ℚ)
    (ideal_mul_zero R I hI)
    (by intro q x;change ((q • x : I):R)=algebraMap ℚ R q*(x:R);rw [Submodule.coe_smul_of_tower,Algebra.smul_def])
    (by intro q x;rw [op_smul_eq_smul];change ((q • x : I):R)=(x:R)*algebraMap ℚ R q;rw [Submodule.coe_smul_of_tower,Algebra.smul_def];exact mul_comm _ _)

theorem splitLift_to_idealLift (d : augDeriv ε I) :
    (squareZeroToRing R I hI).comp (lift ε d)=idealLift ε R I hI d := by
  apply AlgHom.ext
  intro a
  rfl

@[simp] theorem squareZeroToRing_apply (x : TrivSqZeroExt ℚ I) :
    squareZeroToRing R I hI x=algebraMap ℚ R x.fst+(x.snd:R) := rfl

theorem squareZeroToRing_reduction :
    (Ideal.Quotient.mkₐ ℚ I).comp (squareZeroToRing R I hI)=
      (Algebra.ofId ℚ (R⧸I)).comp (TrivSqZeroExt.fstHom ℚ ℚ I) := by
  apply AlgHom.ext
  intro x
  change Ideal.Quotient.mk I (squareZeroToRing R I hI x)=algebraMap ℚ (R⧸I) x.fst
  rw [squareZeroToRing_apply,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr x.snd.property,add_zero]
  exact (Ideal.Quotient.mkₐ ℚ I).commutes x.fst

end FourCorner.ThetaLocalSurvival.Augmented
