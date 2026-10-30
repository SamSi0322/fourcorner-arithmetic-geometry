import ThetaCoverClassPortable.geometry.AdjacentCoordinateAlgebra
import ThetaCoverClassPortable.geometry.PolynomialCoordinateBaseChange

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Slot03Adjacent
open Polynomial
open scoped TensorProduct
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]

def conicEquiv (c : K) :
    L ⊗[K] AdjacentConicLiteralModel.CoordinateRing c ≃ₐ[L]
      AdjacentConicLiteralModel.CoordinateRing (algebraMap K L c) := by
  let e := (polyEquivTensor' K L).symm
  let p := AdjacentConicPresentation.literalEquation c (c^2-1)
  let q := AdjacentConicPresentation.literalEquation (algebraMap K L c) ((algebraMap K L c)^2-1)
  exact (AdjoinRoot.tensorAlgEquiv (R := K) (T := L) p
    (p.map (Algebra.TensorProduct.includeRight : K[X] →ₐ[K] L ⊗[K] K[X]).toRingHom) rfl).trans
    (AdjoinRoot.mapAlgEquiv e _ q (by
      apply Associated.of_eq
      simp [p, q, AdjacentConicPresentation.literalEquation, Polynomial.map_map, e]))

@[simp] theorem conicEquiv_U (c : K) : conicEquiv (L := L) c
    (1 ⊗ₜ[K] AdjacentConicLiteralModel.coordinateU c) =
      AdjacentConicLiteralModel.coordinateU (algebraMap K L c) := by
  unfold conicEquiv AdjacentConicLiteralModel.coordinateU AdjacentConicPresentation.coordinateU
  simp only [AdjoinRoot.algebraMap_eq]
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of, AdjoinRoot.coe_mapAlgEquiv,
    AdjoinRoot.map_of]
  simp

@[simp] theorem conicEquiv_V (c : K) : conicEquiv (L := L) c
    (1 ⊗ₜ[K] AdjacentConicLiteralModel.coordinateV c) =
      AdjacentConicLiteralModel.coordinateV (algebraMap K L c) := by
  unfold conicEquiv AdjacentConicLiteralModel.coordinateV AdjacentConicPresentation.coordinateV
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root, AdjoinRoot.coe_mapAlgEquiv,
    AdjoinRoot.map_root]

@[simp] theorem conicEquiv_radicand (c : K) (i : Fin 2) :
    conicEquiv (L := L) c (1 ⊗ₜ[K] AdjacentConicRadicands.radicand c i) =
      AdjacentConicRadicands.radicand (algebraMap K L c) i := by
  let f := ((conicEquiv (L := L) c).toAlgHom.restrictScalars K).comp
    (Algebra.TensorProduct.includeRight :
      AdjacentConicLiteralModel.CoordinateRing c →ₐ[K]
        L ⊗[K] AdjacentConicLiteralModel.CoordinateRing c)
  have hu : f (AdjacentConicLiteralModel.coordinateU c) =
      AdjacentConicLiteralModel.coordinateU (algebraMap K L c) := conicEquiv_U c
  have hv : f (AdjacentConicLiteralModel.coordinateV c) =
      AdjacentConicLiteralModel.coordinateV (algebraMap K L c) := conicEquiv_V c
  change f (AdjacentConicRadicands.radicand c i) = _
  fin_cases i <;> simp only [AdjacentConicRadicands.radicand, map_add,
    map_sub, map_pow, map_one, map_ofNat, hu, hv]

def coordinateEquiv (c : K) :
    L ⊗[K] AdjacentCoordinateAlgebra.CoordinateRing c ≃ₐ[L]
      AdjacentCoordinateAlgebra.CoordinateRing (algebraMap K L c) := by
  let e := conicEquiv (L := L) c
  have h0 := conicEquiv_radicand (L := L) c 0
  have h1 := conicEquiv_radicand (L := L) c 1
  exact (Multiquadratic.BaseChange.stage₂Equiv e
    (AdjacentConicRadicands.radicand c 0) (AdjacentConicRadicands.radicand c 1)).trans
      (by rw [h0, h1]; exact AlgEquiv.refl)

theorem tensor_domain (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1)
    (L : Type*) [Field L] [Algebra ℚ L] :
    IsDomain (L ⊗[ℚ] AdjacentCoordinateAlgebra.CoordinateRing c) := by
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hmap : algebraMap ℚ L c = (c : L) :=
    RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ L) (Rat.castHom L)) c
  letI : IsDomain (AdjacentCoordinateAlgebra.CoordinateRing (algebraMap ℚ L c)) := by
    rw [hmap]
    exact AdjacentCoordinateAlgebra.rational_coordinateRing_isDomain (K := L) c hc h1
  exact Function.Injective.isDomain (coordinateEquiv (L := L) c)
    (coordinateEquiv (L := L) c).injective

#print axioms conicEquiv
#print axioms coordinateEquiv
#print axioms tensor_domain
end FourCorner.Slot03Adjacent
