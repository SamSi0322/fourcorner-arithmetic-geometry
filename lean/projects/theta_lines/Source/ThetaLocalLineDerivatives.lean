import ThetaOrderTwoDerivativeEvaluation

namespace FourCorner.ThetaLocalLineDerivatives
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDExactChartTransitions ThetaDActualDifferential
open ThetaDifferentialChartIdentity ThetaContactTangencyCertificates ThetaActualLineDifferentials
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra

 theorem Dx : KaehlerDifferential.D K field x = Fy x y • omega := by
  rw [omega,smul_smul,mul_inv_cancel₀ Fy_ne_zero,one_smul]

 theorem Dy : KaehlerDifferential.D K field y = (-Fx x y) • omega := by
  calc
    KaehlerDifferential.D K field y = (Fy x y)⁻¹ • (Fy x y • KaehlerDifferential.D K field y) := by
      rw [smul_smul,inv_mul_cancel₀ Fy_ne_zero,one_smul]
    _ = (Fy x y)⁻¹ • -(Fx x y • KaehlerDifferential.D K field x) := by
      rw [eq_neg_of_add_eq_zero_right ThetaDFiniteDifferential.differential_relation]
    _ = (-Fx x y) • omega := by
      simp only [omega,smul_neg,←neg_smul,smul_smul]
      congr 1
      ring

 theorem DuY : KaehlerDifferential.D K field uY = (-YFv uY vY) • (y • omega) := by
  rw [YZ_transition.1,div_eq_mul_inv,Derivation.leibniz,Derivation.leibniz_inv,Dx,Dy]
  simp only [YZ_transition.2,smul_smul,←neg_smul,←add_smul]
  congr 1
  unfold Fy Fx YFv
  field_simp [y_ne_zero]
  have h := polynomial_relation
  linear_combination 4*h

 theorem DvY : KaehlerDifferential.D K field vY = YFu uY vY • (y • omega) := by
  rw [YZ_transition.2,Derivation.leibniz_inv,Dy]
  simp only [YZ_transition.1,smul_smul,←neg_smul]
  congr 1
  unfold Fx YFu
  field_simp [y_ne_zero]
  ring

 theorem Du : KaehlerDifferential.D K field u = YFv u v • (x • omega) := by
  rw [XZ_transition.1,div_eq_mul_inv,Derivation.leibniz,Derivation.leibniz_inv,Dx,Dy]
  simp only [XZ_transition.2,smul_smul,←neg_smul,←add_smul]
  congr 1
  unfold Fy Fx YFv
  field_simp [x_ne_zero]
  have h := polynomial_relation
  linear_combination -4*h

 theorem Dv : KaehlerDifferential.D K field v = (-YFu u v) • (x • omega) := by
  rw [XZ_transition.2,Derivation.leibniz_inv,Dx]
  simp only [XZ_transition.1,smul_smul]
  congr 1
  unfold Fy YFu
  field_simp [x_ne_zero]
  ring

 theorem affine_Y (α β : K) :
    KaehlerDifferential.D K field (affineFunction α β)=
      (YFu uY vY+algebraMap K field α*YFv uY vY) • (y • omega) := by
  rw [D_affineFunction,DuY,DvY]
  module

 theorem vertical_Z (t : K) :
    KaehlerDifferential.D K field (verticalFunction t)=
      (ZFy x y+algebraMap K field t*ZFx x y) • omega := by
  rw [D_verticalFunction,Dx,Dy]
  change _=(Fy x y+algebraMap K field t*Fx x y) • omega
  module

#print axioms DuY
#print axioms DvY
#print axioms Du
#print axioms Dv
#print axioms affine_Y
#print axioms vertical_Z
end
end FourCorner.ThetaLocalLineDerivatives
