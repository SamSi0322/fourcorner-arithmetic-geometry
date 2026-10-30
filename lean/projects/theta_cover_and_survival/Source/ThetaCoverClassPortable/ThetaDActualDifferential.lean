import ThetaCoverClassPortable.ThetaDFieldCoordinates
import ThetaCoverClassPortable.Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental

namespace FourCorner.ThetaDActualDifferential
open AlgebraicGeometry AlgebraicCurve MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates
open scoped TensorProduct
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra

 theorem minus_relation (a : Fin 1) :
    MvPolynomial.aeval ![(-1:K),1] (ThetaDGeometricChartPoints.equation 2 a)=0 := by
  fin_cases a
  norm_num [ThetaDGeometricChartPoints.equation,ThetaQuotientChart.affineEquation,
    ThetaAmbientChart.dehom,targetEquation,targetPolynomial,ThetaTargetSmooth.drop_table,Fin.isValue]
  simp
  norm_num

def minusEvaluation : K ⊗[ℚ] chartRing 2 →ₐ[K] K :=
  { (Algebra.TensorProduct.lift (AlgHom.id ℚ K)
      (ThetaDGeometricChartPoints.evaluation 2 ![-1,1] minus_relation)
      (fun _ _ => Commute.all _ _)).toRingHom with
    commutes' := by intro k;simp [Algebra.TensorProduct.algebraMap_apply,Algebra.TensorProduct.lift_tmul] }

/-- Nonconstancy in the ACTUAL native function field: both evaluations are
on the actual affine section ring already identified above. -/
theorem x_not_constant (c : K) : x ≠ algebraMap K field c := by
  intro hc
  let t : K ⊗[ℚ] chartRing 2 := 1 ⊗ₜ[ℚ] (Ideal.Quotient.mk _ (X (0:Fin 2)))
  have ht : t=c ⊗ₜ[ℚ] (1 : chartRing 2) := by
    apply chartToField_injective 2
    calc
      chartToField 2 t=x := rfl
      _=algebraMap K field c := hc
      _=chartToField 2 (c ⊗ₜ[ℚ] (1 : chartRing 2)) := by
        simpa only [Algebra.TensorProduct.algebraMap_apply,show algebraMap K K c=c from rfl] using ((chartToField 2).commutes c).symm
  have hp := congrArg (tensorEvaluation 2) ht
  have hm := congrArg minusEvaluation ht
  have ep : tensorEvaluation 2 t=1 := evaluate_coordinate 2 0
  have em : minusEvaluation t = -1 := by
    simp [minusEvaluation,t,Algebra.TensorProduct.lift_tmul]
  rw [ep] at hp
  rw [em] at hm
  have epc : tensorEvaluation 2 (c ⊗ₜ[ℚ] (1 : chartRing 2))=c := by
    simpa only [Algebra.TensorProduct.algebraMap_apply,show algebraMap K K c=c from rfl] using (tensorEvaluation 2).commutes c
  have emc : minusEvaluation (c ⊗ₜ[ℚ] (1 : chartRing 2))=c := by
    simpa only [Algebra.TensorProduct.algebraMap_apply,show algebraMap K K c=c from rfl] using minusEvaluation.commutes c
  rw [epc] at hp
  rw [emc] at hm
  have hh : (1:K)=(-1:K) := hp.trans hm.symm
  norm_num at hh

 theorem constant_of_isAlgebraic {z : field} (hz : IsAlgebraic K z) :
    ∃c : K,algebraMap K field c=z := by
  have hi := hz.isIntegral
  have hq : (minpoly K z).leadingCoeff=1 := minpoly.monic hi
  have hd : (minpoly K z).degree=1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi)
  have h : Polynomial.aeval z (minpoly K z)=0 := minpoly.aeval K z
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd,hq,Polynomial.C_1,one_mul,
    Polynomial.aeval_add,Polynomial.aeval_X,Polynomial.aeval_C,add_eq_zero_iff_eq_neg] at h
  exact ⟨-(minpoly K z).coeff 0,by rw [map_neg];exact h.symm⟩

 theorem x_transcendental : Transcendental K x := by
  intro ha
  obtain ⟨c,hc⟩ := constant_of_isAlgebraic ha
  exact x_not_constant c hc.symm

 theorem dx_ne_zero : KaehlerDifferential.D K field x ≠ 0 := by
  letI : CharZero field := charZero_of_injective_algebraMap (algebraMap K field).injective
  letI : IsCurveOver K field := field_isCurveOver
  letI : Algebra.EssFiniteType K field := field_essFiniteType
  obtain ⟨t,ht,hfd,_⟩ := IsCurveOver.exists_separating_transcendental (K:=K) (F:=field)
  letI := hfd
  letI : FiniteDimensional (IntermediateField.adjoin K ({x}:Set field)) field :=
    finiteDimensional_adjoin_of_transcendental t x_transcendental
  letI : Algebra.IsSeparable (IntermediateField.adjoin K ({x}:Set field)) field := inferInstance
  exact KaehlerDifferential.D_ne_zero_of_transcendental K x x_transcendental

/-- An actual nonzero rational differential on the original geometric D;
regularity and its exact divisor are separate proof obligations. -/
def omega : Ω[field⁄K] :=
  (ThetaDifferentialChartIdentity.Fy x y)⁻¹ • KaehlerDifferential.D K field x

 theorem omega_ne_zero : omega ≠ 0 := by
  exact smul_ne_zero (inv_ne_zero Fy_ne_zero) dx_ne_zero

 theorem x_ne_zero : x ≠ 0 := fun h => x_transcendental (h ▸ isAlgebraic_zero)

 theorem actual_omega_transition :
    omega=(-(x⁻¹)/ThetaDifferentialChartIdentity.Gu (y/x) x⁻¹) •
      KaehlerDifferential.D K field (x⁻¹) :=
  ThetaDifferentialChartIdentity.omega_transition x y x_ne_zero Fy_ne_zero

#print axioms x_not_constant
#print axioms x_transcendental
#print axioms dx_ne_zero
#print axioms omega_ne_zero
#print axioms actual_omega_transition
end
end FourCorner.ThetaDActualDifferential
