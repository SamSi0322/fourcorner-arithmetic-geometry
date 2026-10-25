import PaperLogIdentification

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open Polynomial
open scoped TensorProduct
variable {K : Type*} [Field K]

/-- The original curve's actual affine coordinate generators. -/
def curveCoordinateX (W : WeierstrassCurve K) : W.toAffine.CoordinateRing :=
  AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C Polynomial.X)
def curveCoordinateY (W : WeierstrassCurve K) : W.toAffine.CoordinateRing :=
  AdjoinRoot.root W.toAffine.polynomial

theorem coordinatePolynomial_root (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    W.toAffine.polynomial.eval₂ (Polynomial.aeval (formalX W) : K[X] →ₐ[K] FormalFrac K).toRingHom (formalY W)=0 := by
  simpa [WeierstrassCurve.Affine.polynomial,WeierstrassCurve.toAffine,h1,h2,h3,h6,
    Polynomial.aeval_def,Polynomial.eval₂_pow,Polynomial.eval₂_C,Polynomial.aeval_X] using sub_eq_zero.mpr (formal_coordinates_cubic W h1 h2 h3 h6)

/-- The genuine K-algebra evaluation from the ORIGINAL curve coordinate ring
into the actual formal fraction field; its relation is proved, not assumed. -/
def coordinateEvaluation (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    W.toAffine.CoordinateRing →ₐ[K] FormalFrac K :=
  AdjoinRoot.liftAlgHom W.toAffine.polynomial (Polynomial.aeval (formalX W)) (formalY W)
    (coordinatePolynomial_root W h1 h2 h3 h6)

theorem coordinateEvaluation_X (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    coordinateEvaluation W h1 h2 h3 h6 (curveCoordinateX W)=formalX W := by
  change AdjoinRoot.lift (Polynomial.aeval (formalX W) : K[X] →ₐ[K] FormalFrac K).toRingHom (formalY W)
    (coordinatePolynomial_root W h1 h2 h3 h6)
    (AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C Polynomial.X))=formalX W
  rw [AdjoinRoot.lift_mk,Polynomial.eval₂_C]
  exact Polynomial.aeval_X _

theorem coordinateEvaluation_Y (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    coordinateEvaluation W h1 h2 h3 h6 (curveCoordinateY W)=formalY W := by
  change AdjoinRoot.lift (Polynomial.aeval (formalX W) : K[X] →ₐ[K] FormalFrac K).toRingHom (formalY W)
    (coordinatePolynomial_root W h1 h2 h3 h6)
    (AdjoinRoot.root W.toAffine.polynomial)=formalY W
  exact AdjoinRoot.lift_root _

/-- The original denominator 2Y is nonzero at the actual formal point. -/
theorem coordinateEvaluation_denominator [CharZero K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    coordinateEvaluation W h1 h2 h3 h6 (2*curveCoordinateY W) ≠ 0 := by
  rw [map_mul,map_ofNat,coordinateEvaluation_Y]
  exact mul_ne_zero (by norm_num) (formalY_ne_zero W)

@[instance_reducible] def coordinateEvaluationAlgebra (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    Algebra W.toAffine.CoordinateRing (FormalFrac K) :=
  (coordinateEvaluation W h1 h2 h3 h6).toRingHom.toAlgebra

theorem coordinateEvaluation_tower (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    letI := coordinateEvaluationAlgebra W h1 h2 h3 h6
    IsScalarTower K W.toAffine.CoordinateRing (FormalFrac K) := by
  letI := coordinateEvaluationAlgebra W h1 h2 h3 h6
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact ((coordinateEvaluation W h1 h2 h3 h6).commutes a).symm

/-- Native base change of the ORIGINAL curve's Kähler module. Multiplication
by the inverse of the evaluated denominator is legitimate by the preceding
nonvanishing theorem. The native map sends this exact source dx/(2y) to Ω dz. -/
theorem original_coordinate_differential_pullback [CharZero K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    letI := coordinateEvaluationAlgebra W h1 h2 h3 h6
    letI := coordinateEvaluation_tower W h1 h2 h3 h6
    KaehlerDifferential.mapBaseChange K W.toAffine.CoordinateRing (FormalFrac K)
      ((coordinateEvaluation W h1 h2 h3 h6 (2*curveCoordinateY W))⁻¹ •
        ((1:FormalFrac K) ⊗ₜ[W.toAffine.CoordinateRing]
          (KaehlerDifferential.D K W.toAffine.CoordinateRing (curveCoordinateX W))))=
      formalMap (shortOmega W) • (KaehlerDifferential.D K (FormalFrac K)) (formalZ:FormalFrac K) := by
  letI := coordinateEvaluationAlgebra W h1 h2 h3 h6
  letI := coordinateEvaluation_tower W h1 h2 h3 h6
  rw [map_smul,KaehlerDifferential.mapBaseChange_tmul,one_smul,KaehlerDifferential.map_D]
  change (coordinateEvaluation W h1 h2 h3 h6 (2*curveCoordinateY W))⁻¹ •
      (KaehlerDifferential.D K (FormalFrac K))
        (coordinateEvaluation W h1 h2 h3 h6 (curveCoordinateX W))= _
  rw [map_mul,map_ofNat,coordinateEvaluation_X,coordinateEvaluation_Y]
  exact literal_differential_pullback W h1 h2 h3 h6

/-- The coefficient integrated by paperEllSeries is thus identified through
the native source-module map, not merely through renamed field variables. -/
theorem paper_primitive_source_module_pullback [CharZero K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    letI := coordinateEvaluationAlgebra W h1 h2 h3 h6
    letI := coordinateEvaluation_tower W h1 h2 h3 h6
    KaehlerDifferential.mapBaseChange K W.toAffine.CoordinateRing (FormalFrac K)
      ((coordinateEvaluation W h1 h2 h3 h6 (2*curveCoordinateY W))⁻¹ •
        ((1:FormalFrac K) ⊗ₜ[W.toAffine.CoordinateRing]
          (KaehlerDifferential.D K W.toAffine.CoordinateRing (curveCoordinateX W))))=
      formalMap (PowerSeries.derivative K (paperEllSeries W)) •
        (KaehlerDifferential.D K (FormalFrac K)) (formalZ:FormalFrac K) := by
  letI := coordinateEvaluationAlgebra W h1 h2 h3 h6
  letI := coordinateEvaluation_tower W h1 h2 h3 h6
  rw [paperEllSeries,normalizedPrimitive_derivative]
  exact original_coordinate_differential_pullback W h1 h2 h3 h6

#print axioms coordinateEvaluation
#print axioms coordinateEvaluation_X
#print axioms coordinateEvaluation_Y
#print axioms coordinateEvaluation_denominator
#print axioms original_coordinate_differential_pullback
#print axioms paper_primitive_source_module_pullback
end FourCorner.CommonSource.LogPrecision
