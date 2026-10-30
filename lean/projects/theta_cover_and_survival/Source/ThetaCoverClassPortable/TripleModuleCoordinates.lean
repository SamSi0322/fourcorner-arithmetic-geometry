import ThetaCoverClassPortable.PairTripleCoordinates

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
namespace FourCorner.PairCoactionTransfer
open FourCorner.RelativeTensorCancel
universe u
variable (K A D T M : Type u) [CommRing K] [CommRing A] [CommRing D] [CommRing T]
variable [Algebra K A] [Algebra K D] [Algebra K T] [Algebra A D] [Algebra A T]
variable [IsScalarTower K A D] [IsScalarTower K A T]
variable [AddCommGroup M] [Module K M] [Module A M] [Module D M]
variable [IsScalarTower K A M] [IsScalarTower K D M] [IsScalarTower A D M]

/-- Contract ONLY the actual source-D factor against the retained module M.
The output order is target, middle, source module. -/
def tripleContract : tripleRing K D ⊗[D] M →ₗ[K] D ⊗[K] (D ⊗[K] M) :=
  (TensorProduct.assoc K D D M).toLinearMap.comp
    (relativeCancel K K D (D ⊗[K] D) M).toLinearMap

@[simp] theorem tripleContract_tmul (ds dt dm : D) (m : M) :
    tripleContract K D M ((ds ⊗ₜ[K] (dt ⊗ₜ[K] dm)) ⊗ₜ[D] m) =
      dt ⊗ₜ[K] (dm ⊗ₜ[K] (ds • m)) := rfl

/-- Inserting the middle coordinate into a DIRECT arrow is a proved
triple-coordinate formula, retaining the source module. -/
theorem tripleContract_direct (z : D ⊗[K] D) (m : M) :
    tripleContract K D M (directPair K D z ⊗ₜ[D] m) =
      TensorProduct.map (LinearMap.id : D →ₗ[K] D)
        (TensorProduct.mk K D M (1 : D))
        (relativeCancel K K D D M (z ⊗ₜ[D] m)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.zero_tmul]
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
  | tmul ds dt =>
    simp only [directPair_tmul, tripleContract_tmul, relativeCancel_tmul,
      TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.mk_apply]

/-- Two REVERSE-COMPOSABLE arrows contract into target/middle/source
coordinates with the actual shared middle product. -/
theorem tripleContract_left_right (z1 z2 : D ⊗[K] D) (m : M) :
    tripleContract K D M ((leftPair K D z1 * rightPair K D z2) ⊗ₜ[D] m) =
      relativeCancel K K D D (D ⊗[K] M)
        (z1 ⊗ₜ[D] relativeCancel K K D D M (z2 ⊗ₜ[D] m)) := by
  induction z1 using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul, TensorProduct.zero_tmul]
  | add x y hx hy => simp only [map_add, add_mul, TensorProduct.add_tmul, hx, hy]
  | tmul s1 t1 =>
    induction z2 using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero, TensorProduct.zero_tmul, TensorProduct.tmul_zero]
    | add x y hx hy =>
      simp only [map_add, mul_add, TensorProduct.add_tmul, TensorProduct.tmul_add, hx, hy]
    | tmul s2 t2 =>
      simp only [leftPair_tmul, rightPair_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one, tripleContract_tmul, relativeCancel_tmul,
        TensorProduct.smul_tmul', smul_eq_mul]

/-- Actual base-change extension of a compatible coefficient map, by the
balanced tensor universal property. No coaction equation is an input. -/
def coefficientLift (phi : T →+* tripleRing K D)
    (hphi : ∀ a, phi (algebraMap A T a) = algebraMap A (tripleRing K D) a) :
    D ⊗[A] T →ₐ[D] tripleRing K D :=
  Algebra.TensorProduct.lift (Algebra.ofId D (tripleRing K D))
    ({ phi with commutes' := hphi } : T →ₐ[A] tripleRing K D) (fun _ _ => Commute.all _ _)

@[simp] theorem coefficientLift_tmul (phi : T →+* tripleRing K D)
    (hphi : ∀ a, phi (algebraMap A T a) = algebraMap A (tripleRing K D) a)
    (d : D) (b : T) :
    coefficientLift K A D T phi hphi (d ⊗ₜ[A] b) = tripleSource K D d * phi b := by
  simp [coefficientLift, tripleSource]

/-- The genuine linear map transporting original composable coefficients
and the SAME module M into pair-target/middle/source coordinates. -/
def coefficientCoordinates (phi : T →+* tripleRing K D)
    (hphi : ∀ a, phi (algebraMap A T a) = algebraMap A (tripleRing K D) a) :
    T ⊗[A] M →ₗ[K] D ⊗[K] (D ⊗[K] M) :=
  (tripleContract K D M).comp
    (((TensorProduct.map (coefficientLift K A D T phi hphi).toLinearMap
      (LinearMap.id : M →ₗ[D] M)).restrictScalars K).comp
      (relativeCancel K A D T M).symm.toLinearMap)

 theorem coefficientCoordinates_tmul (phi : T →+* tripleRing K D)
    (hphi : ∀ a, phi (algebraMap A T a) = algebraMap A (tripleRing K D) a)
    (b : T) (m : M) :
    coefficientCoordinates K A D T M phi hphi (b ⊗ₜ[A] m) =
      tripleContract K D M (phi b ⊗ₜ[D] m) := by
  simp only [coefficientCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    relativeCancel_symm_tmul, LinearMap.restrictScalars_apply, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, coefficientLift_tmul, LinearMap.id_apply, map_one, one_mul]

end FourCorner.PairCoactionTransfer
