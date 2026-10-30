import ThetaDPlaneChartSections
import ThetaDifferentialChartIdentity

namespace FourCorner.ThetaDFieldCoordinates
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections
open scoped TensorProduct
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : Algebra ℚ field := ((algebraMap K field).comp (algebraMap ℚ K)).toAlgebra
local instance sectionsAlgebra (j : Fin 3) : Algebra K Γ(geometricD,geoU j) :=
  Scheme.TwoAffineOpenCover.algebraOfHom toBase (geoU j)

 theorem ones_relation (j : Fin 3) (a : Fin 1) :
    MvPolynomial.aeval (fun _ : Fin 2 => (1:K)) (ThetaDGeometricChartPoints.equation j a)=0 := by
  have h20 : (2:Fin 3) ≠ 0 := by decide
  have h21 : (2:Fin 3) ≠ 1 := by decide
  fin_cases j <;> fin_cases a <;>
    norm_num [ThetaDGeometricChartPoints.equation,ThetaQuotientChart.affineEquation,
      ThetaAmbientChart.dehom,targetEquation,targetPolynomial,ThetaTargetSmooth.drop_table,Fin.isValue,h20,h21] <;> simp <;> norm_num

def tensorEvaluation (j : Fin 3) : K ⊗[ℚ] chartRing j →ₐ[K] K :=
  { (Algebra.TensorProduct.lift (AlgHom.id ℚ K)
      (ThetaDGeometricChartPoints.evaluation j (fun _=>1) (ones_relation j))
      (fun _ _ => Commute.all _ _)).toRingHom with
    commutes' := by intro k;simp [Algebra.TensorProduct.algebraMap_apply,Algebra.TensorProduct.lift_tmul] }

def evaluation (j : Fin 3) : Γ(geometricD,geoU j) →ₐ[K] K :=
  (tensorEvaluation j).comp (actualChartEquiv j).symm.toAlgHom

/-- Every one of the three ACTUAL base-changed affine opens is nonempty,
proved using evaluation on its actual section ring. -/
theorem geoU_nonempty (j : Fin 3) : Nonempty (geoU j) := by
  let p : PrimeSpectrum Γ(geometricD,geoU j) :=
    PrimeSpectrum.comap (evaluation j).toRingHom (⊥ : PrimeSpectrum K)
  exact ⟨(affine_geoU j).isoSpec.inv p⟩
local instance (j : Fin 3) : Nonempty (geoU j) := geoU_nonempty j

def germ (j : Fin 3) : Γ(geometricD,geoU j) →ₐ[K] field :=
  { (geometricD.germToFunctionField (geoU j)).hom with
    commutes' := germToFunctionField_algebraMap toBase (geoU j) }

def chartToField (j : Fin 3) : K ⊗[ℚ] chartRing j →ₐ[K] field :=
  (germ j).comp (actualChartEquiv j).toAlgHom

theorem chartToField_injective (j : Fin 3) : Function.Injective (chartToField j) :=
  (geometricD.germToFunctionField_injective (geoU j)).comp (actualChartEquiv j).injective

/-- Literal affine coordinates, as elements of the native function field of
original D_Qbar, via its actual affine section rings. -/
def coordinate (j : Fin 3) (a : Fin 2) : field :=
  chartToField j (1 ⊗ₜ[ℚ] (Ideal.Quotient.mk _ (X a)))

def rationalChartMap (j : Fin 3) : chartRing j →ₐ[ℚ] field :=
  { ((chartToField j).toRingHom.comp
      (Algebra.TensorProduct.includeRight : chartRing j →ₐ[ℚ] K ⊗[ℚ] chartRing j).toRingHom) with
    commutes' := by
      intro q
      exact RingHom.congr_fun (Subsingleton.elim
        (((chartToField j).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom).comp (algebraMap ℚ (chartRing j)))
        (algebraMap ℚ field)) q }

 theorem field_relation (j : Fin 3) (a : Fin 1) :
    ThetaTargetSmooth.eqScalar j a (coordinate j)=0 :=
  ThetaTargetSmooth.relations j (rationalChartMap j) a

abbrev x : field := coordinate 2 0
abbrev y : field := coordinate 2 1

 theorem polynomial_relation :
    9801*x^4+19598*x^2*y^2-39592*x^2+9801*y^4-39592*y^2+39984=0 :=
  field_relation 2 0

 theorem evaluate_coordinate (j : Fin 3) (a : Fin 2) :
    tensorEvaluation j (1 ⊗ₜ[ℚ] (Ideal.Quotient.mk _ (X a)))=1 := by
  simp [tensorEvaluation,Algebra.TensorProduct.lift_tmul]

 theorem Fy_ne_zero : ThetaDifferentialChartIdentity.Fy x y ≠ 0 := by
  intro h
  let u : K ⊗[ℚ] chartRing 2 := 1 ⊗ₜ[ℚ] (Ideal.Quotient.mk _ (X (0:Fin 2)))
  let v : K ⊗[ℚ] chartRing 2 := 1 ⊗ₜ[ℚ] (Ideal.Quotient.mk _ (X (1:Fin 2)))
  have hc (n:ℕ) [n.AtLeastTwo] : chartToField 2 (OfNat.ofNat n : K ⊗[ℚ] chartRing 2)=(OfNat.ofNat n:field) := map_ofNat (chartToField 2).toRingHom n
  have hp (z : K ⊗[ℚ] chartRing 2) (n:ℕ) : chartToField 2 (z^n)=(chartToField 2 z)^n := map_pow (chartToField 2).toRingHom z n
  have ux : chartToField 2 u=x := rfl
  have vy : chartToField 2 v=y := rfl
  have hh : v*(39196*u^2+39204*v^2-79184)=0 := by
    apply chartToField_injective 2
    simpa only [map_mul,map_add,map_sub,hp,hc,map_zero,ux,vy,ThetaDifferentialChartIdentity.Fy] using h
  have he := congrArg (tensorEvaluation 2) hh
  have hu : tensorEvaluation 2 u=1 := evaluate_coordinate 2 0
  have hv : tensorEvaluation 2 v=1 := evaluate_coordinate 2 1
  have ec (n:ℕ) [n.AtLeastTwo] : tensorEvaluation 2 (OfNat.ofNat n : K ⊗[ℚ] chartRing 2)=(OfNat.ofNat n:K) := map_ofNat (tensorEvaluation 2).toRingHom n
  have ep (z : K ⊗[ℚ] chartRing 2) (n:ℕ) : tensorEvaluation 2 (z^n)=(tensorEvaluation 2 z)^n := map_pow (tensorEvaluation 2).toRingHom z n
  simp only [map_mul,map_add,map_sub,ep,ec,map_zero,hu,hv] at he
  norm_num at he

#print axioms geoU_nonempty
#print axioms chartToField_injective
#print axioms polynomial_relation
#print axioms Fy_ne_zero
end
end FourCorner.ThetaDFieldCoordinates
