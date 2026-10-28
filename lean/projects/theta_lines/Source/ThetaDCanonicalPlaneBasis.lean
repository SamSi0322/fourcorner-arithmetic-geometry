import ThetaDPlaneRegularForms

namespace FourCorner.ThetaDCanonicalPlaneBasis
open AlgebraicGeometry AlgebraicCurve MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates
open ThetaDActualDifferential ThetaRegularFunctionDifferential ThetaDGlobalCanonicalCandidate ThetaDPlaneRegularForms
open scoped TensorProduct
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : Module.Finite K (regularDifferentials K field) := regular_dimension_three.1

 theorem yminus_relation (a : Fin 1) :
    MvPolynomial.aeval ![(1:K),-1] (ThetaDGeometricChartPoints.equation 2 a)=0 := by
  fin_cases a
  norm_num [ThetaDGeometricChartPoints.equation,ThetaQuotientChart.affineEquation,
    ThetaAmbientChart.dehom,targetEquation,targetPolynomial,ThetaTargetSmooth.drop_table,Fin.isValue]
  simp
  norm_num

def yminusEvaluation : K ⊗[ℚ] chartRing 2 →ₐ[K] K :=
  { (Algebra.TensorProduct.lift (AlgHom.id ℚ K)
      (ThetaDGeometricChartPoints.evaluation 2 ![1,-1] yminus_relation)
      (fun _ _=>Commute.all _ _)).toRingHom with
    commutes' := by intro k;simp [Algebra.TensorProduct.algebraMap_apply,Algebra.TensorProduct.lift_tmul] }

 theorem scalar_tmul {E : Type*} [CommRing E] [Algebra K E]
    (f : K ⊗[ℚ] chartRing 2 →ₐ[K] E) (c : K) :
    f (c ⊗ₜ[ℚ] (1 : chartRing 2))=algebraMap K E c := by
  simpa only [Algebra.TensorProduct.algebraMap_apply,show algebraMap K K c=c from rfl] using f.commutes c

 theorem evaluation_scalar (f : K ⊗[ℚ] chartRing 2 →ₐ[K] K) (c : K) :
    f (c ⊗ₜ[ℚ] (1 : chartRing 2))=c := scalar_tmul f c

/-- Literal 1,x,y are K-linearly independent in the TRUE original geometric
function field, proved using three actual affine-ring evaluations. -/
theorem linear_form_zero (a b c : K)
    (h : algebraMap K field a+algebraMap K field b*x+algebraMap K field c*y=0) :
    a=0 ∧ b=0 ∧ c=0 := by
  let T := K ⊗[ℚ] chartRing 2
  let U : T := 1 ⊗ₜ[ℚ] (Ideal.Quotient.mk _ (X (0:Fin 2)))
  let V : T := 1 ⊗ₜ[ℚ] (Ideal.Quotient.mk _ (X (1:Fin 2)))
  let C : K → T := fun k=>k ⊗ₜ[ℚ] (1:chartRing 2)
  have hu : chartToField 2 U=x := rfl
  have hv : chartToField 2 V=y := rfl
  have ht : C a+C b*U+C c*V=0 := by
    apply chartToField_injective 2
    simpa only [map_add,map_mul,map_zero,C,scalar_tmul,hu,hv] using h
  have hp := congrArg (tensorEvaluation 2) ht
  have hm := congrArg ThetaDActualDifferential.minusEvaluation ht
  have hy := congrArg yminusEvaluation ht
  have epU : tensorEvaluation 2 U=1 := evaluate_coordinate 2 0
  have epV : tensorEvaluation 2 V=1 := evaluate_coordinate 2 1
  have emU : ThetaDActualDifferential.minusEvaluation U=(-1:K) := by
    simp [ThetaDActualDifferential.minusEvaluation,U,Algebra.TensorProduct.lift_tmul]
  have emV : ThetaDActualDifferential.minusEvaluation V=(1:K) := by
    simp [ThetaDActualDifferential.minusEvaluation,V,Algebra.TensorProduct.lift_tmul]
  have eyU : yminusEvaluation U=(1:K) := by
    simp [yminusEvaluation,U,Algebra.TensorProduct.lift_tmul]
  have eyV : yminusEvaluation V=(-1:K) := by
    simp [yminusEvaluation,V,Algebra.TensorProduct.lift_tmul]
  simp only [map_add,map_mul,map_zero,C,evaluation_scalar,epU,epV,mul_one] at hp
  simp only [map_add,map_mul,map_zero,C,evaluation_scalar,emU,emV,mul_one,mul_neg,neg_mul] at hm
  simp only [map_add,map_mul,map_zero,C,evaluation_scalar,eyU,eyV,mul_one,mul_neg,neg_mul] at hy
  refine ⟨?_,?_,?_⟩
  · linear_combination (1/2)*hm+(1/2)*hy
  · linear_combination (1/2)*hp-(1/2)*hm
  · linear_combination (1/2)*hp-(1/2)*hy

/-- These are elements of the ACTUAL native regular-differential space. -/
def forms : Fin 3 → regularDifferentials K field :=
  ![⟨omega,omega_regular⟩,⟨x • omega,xomega_regular⟩,⟨y • omega,yomega_regular⟩]

 theorem forms_independent : LinearIndependent K forms := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  have hh := congrArg (fun z : regularDifferentials K field => (z:Ω[field⁄K])) hg
  have hh' : g 0 • omega+g 1 • (x • omega)+g 2 • (y • omega)=0 := by
    simpa [Fin.sum_univ_three,forms] using hh
  rw [algebra_compatible_smul field (g 0) omega,
    algebra_compatible_smul field (g 1) (x • omega),
    algebra_compatible_smul field (g 2) (y • omega),smul_smul,smul_smul] at hh'
  have hs : (algebraMap K field (g 0)+algebraMap K field (g 1)*x+
      algebraMap K field (g 2)*y) • omega=0 := by
    simpa only [add_smul] using hh' 
  have hz : algebraMap K field (g 0)+algebraMap K field (g 1)*x+algebraMap K field (g 2)*y=0 :=
    (smul_eq_zero.mp hs).resolve_right omega_ne_zero
  obtain ⟨h0,h1,h2⟩ := linear_form_zero (g 0) (g 1) (g 2) hz
  intro i
  fin_cases i <;> assumption

/-- A genuine basis, now proved from native regularity, literal coordinates,
actual independence, and the independently proved original genus three. -/
def basis : Module.Basis (Fin 3) K (regularDifferentials K field) :=
  basisOfLinearIndependentOfCardEqFinrank forms_independent (by simpa using regular_dimension_three.2.symm)

 theorem basis_eq_forms : (basis : Fin 3 → regularDifferentials K field)=forms :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

#print axioms linear_form_zero
#print axioms forms_independent
#print axioms basis
#print axioms basis_eq_forms
end
end FourCorner.ThetaDCanonicalPlaneBasis
