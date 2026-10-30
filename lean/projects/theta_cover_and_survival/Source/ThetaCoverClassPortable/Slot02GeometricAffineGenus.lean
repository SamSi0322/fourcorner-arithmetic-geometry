import ThetaCoverClassPortable.geometry.OppositeSchemeGenus
import ThetaCoverClassPortable.geometry.OppositeFieldGeometricIntegral
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace FourCorner.OppositeGeometricAffine
open OppositeCoordinateAlgebra OppositePolynomials
universe u
variable {K L : Type u} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

abbrev tensorRing (mu nu : K) := L ⊗[K] ring mu nu

def tensorScheme (mu nu : K) : Scheme := Spec (.of (tensorRing (L := L) mu nu))

/-- This is an actual pullback of the rational affine coordinate scheme. -/
def tensorSchemeIsoPullback (mu nu : K) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.map (CommRingCat.ofHom (algebraMap K (ring mu nu)))) ≅
        tensorScheme (L := L) mu nu :=
  pullbackSpecIso K L (ring mu nu)

section Nondegenerate
variable {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0)

include hmu hnu hA hB hS in
theorem tensorScheme_integral : IsIntegral (tensorScheme (L := L) mu nu) := by
  letI := baseChange_isDomain (L := L) hmu hnu hA hB hS
  unfold tensorScheme
  infer_instance

end Nondegenerate
section FunctionField
variable (mu nu : K) [IsDomain (tensorRing (L := L) mu nu)]

abbrev affineField := (Spec (.of (tensorRing (L := L) mu nu))).functionField

instance affineFieldRingAlgebra :
    Algebra (tensorRing (L := L) mu nu) (affineField (L := L) mu nu) :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (tensorRing (L := L) mu nu))

def affineFieldAlgebra : Algebra L (affineField (L := L) mu nu) :=
  ((algebraMap (tensorRing (L := L) mu nu) (affineField (L := L) mu nu)).comp
    (algebraMap L (tensorRing (L := L) mu nu))).toAlgebra

theorem affineField_tower :
    letI := affineFieldAlgebra (L := L) mu nu
    IsScalarTower L (tensorRing (L := L) mu nu) (affineField (L := L) mu nu) := by
  letI := affineFieldAlgebra (L := L) mu nu
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

instance affineField_fraction : IsFractionRing (tensorRing (L := L) mu nu)
    (affineField (L := L) mu nu) :=
  functionField_isFractionRing_of_affine (.of (tensorRing (L := L) mu nu))

/-- The actual generic-point stalk of the scalar-extended affine scheme. -/
def fractionToAffineField :
    letI := affineFieldAlgebra (L := L) mu nu
    FractionRing (tensorRing (L := L) mu nu) ≃ₐ[L] affineField (L := L) mu nu := by
  letI := affineFieldAlgebra (L := L) mu nu
  letI := affineField_tower (L := L) mu nu
  exact (IsLocalization.algEquiv (nonZeroDivisors (tensorRing (L := L) mu nu))
    (FractionRing (tensorRing (L := L) mu nu)) (affineField (L := L) mu nu)).restrictScalars L

end FunctionField

/-- Genus five for the canonical tensor-product fraction field. -/
theorem tensor_fraction_genus [IsAlgClosed L] {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    letI := baseChange_isDomain (L := L) hmu hnu hA hB hS
    genusFF L (FractionRing (tensorRing (L := L) mu nu)) = 5 := by
  letI := baseChange_isDomain (L := L) hmu hnu hA hB hS
  have hm := (map_ne_zero (algebraMap K L)).2 hmu
  have hn := (map_ne_zero (algebraMap K L)).2 hnu
  have ha : A (algebraMap K L mu) (algebraMap K L nu) ≠ 0 := by
    simpa only [A_map] using (map_ne_zero (algebraMap K L)).2 hA
  have hb : B (algebraMap K L mu) (algebraMap K L nu) ≠ 0 := by
    simpa only [B_map] using (map_ne_zero (algebraMap K L)).2 hB
  have hs : S (algebraMap K L mu) (algebraMap K L nu) ≠ 0 := by
    simpa only [S_map] using (map_ne_zero (algebraMap K L)).2 hS
  letI := coordinateRing_isDomain hm hn ha hb hs
  letI := coordinateRing_isFractionRing hm hn ha hb hs
  let e : FractionRing (tensorRing (L := L) mu nu) ≃ₐ[L]
      FractionRing (ring (algebraMap K L mu) (algebraMap K L nu)) :=
    IsFractionRing.algEquivOfAlgEquiv (baseChangeEquiv (L := L) mu nu)
  let f0 := IsLocalization.algEquiv
    (nonZeroDivisors (ring (algebraMap K L mu) (algebraMap K L nu)))
    (FractionRing (ring (algebraMap K L mu) (algebraMap K L nu)))
    (functionField (algebraMap K L mu) (algebraMap K L nu))
  let f : FractionRing (ring (algebraMap K L mu) (algebraMap K L nu)) ≃ₐ[L]
      functionField (algebraMap K L mu) (algebraMap K L nu) :=
    AlgEquiv.ofRingEquiv (f := f0.toRingEquiv) (by
      intro a
      rw [IsScalarTower.algebraMap_apply L
        (ring (algebraMap K L mu) (algebraMap K L nu))
        (FractionRing (ring (algebraMap K L mu) (algebraMap K L nu)))]
      change f0 (algebraMap (ring (algebraMap K L mu) (algebraMap K L nu)) _
        (algebraMap L (ring (algebraMap K L mu) (algebraMap K L nu)) a)) = _
      rw [f0.commutes]
      change Multiquadratic.CoordinateAlgebra.map₃ (Polynomial L) (RatFunc L) _ _ _
        (algebraMap L (ring (algebraMap K L mu) (algebraMap K L nu)) a) = _
      rw [IsScalarTower.algebraMap_apply L (Polynomial L)
        (ring (algebraMap K L mu) (algebraMap K L nu))]
      rw [Multiquadratic.CoordinateAlgebra.map₃_algebraMap]
      simp only [Polynomial.algebraMap_apply, RatFunc.algebraMap_C]
      rfl)
  exact (genusFF_eq_of_algEquiv (e.trans f)).trans
    (OppositeAffineModel.genus_actual_fractionField hm hn ha hb hs)

/-- The geometric affine scheme's actual generic-point stalk has genus five. -/
theorem affine_stalk_genus [IsAlgClosed L] {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    letI := baseChange_isDomain (L := L) hmu hnu hA hB hS
    letI := affineFieldAlgebra (L := L) mu nu
    genusFF L (affineField (L := L) mu nu) = 5 := by
  letI := baseChange_isDomain (L := L) hmu hnu hA hB hS
  letI := affineFieldAlgebra (L := L) mu nu
  exact (genusFF_eq_of_algEquiv (fractionToAffineField (L := L) mu nu)).symm.trans
    (tensor_fraction_genus (L := L) hmu hnu hA hB hS)

/-- Exact rational-range specialization for the genuine Qbar affine stalk field. -/
theorem rational_affine_stalk_genus (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) :
    letI := OppositeAffineModel.rational_all_field_extensions_integral
      (AlgebraicClosure ℚ) mu nu hnu hpos hlt
    letI := affineFieldAlgebra (L := AlgebraicClosure ℚ) mu nu
    genusFF (AlgebraicClosure ℚ) (affineField (L := AlgebraicClosure ℚ) mu nu) = 5 := by
  have hmu : mu ≠ 0 := by intro hz; simp [hz] at hpos
  exact affine_stalk_genus (L := AlgebraicClosure ℚ) hmu hnu
    (rational_A_ne_zero mu nu hnu) (rational_B_ne_zero mu nu hnu hpos hlt)
    (rational_S_ne_zero mu nu hnu)

end FourCorner.OppositeGeometricAffine
#print axioms FourCorner.OppositeGeometricAffine.tensorSchemeIsoPullback
#print axioms FourCorner.OppositeGeometricAffine.tensorScheme_integral

#print axioms FourCorner.OppositeGeometricAffine.fractionToAffineField
#print axioms FourCorner.OppositeGeometricAffine.tensor_fraction_genus
#print axioms FourCorner.OppositeGeometricAffine.affine_stalk_genus

#print axioms FourCorner.OppositeGeometricAffine.rational_affine_stalk_genus
