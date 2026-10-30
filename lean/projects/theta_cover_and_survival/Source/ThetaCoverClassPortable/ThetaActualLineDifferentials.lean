import ThetaCoverClassPortable.ThetaContactTangencyCertificates
import ThetaCoverClassPortable.ThetaDNaturalGlobalDifferentials

namespace FourCorner.ThetaActualLineDifferentials
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDExactChartTransitions
open ThetaDActualDifferential ThetaDCanonicalPlaneBasis ThetaContactTangencyCertificates
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

 theorem Y_polynomial_relation :
    9801*uY^4+19598*uY^2+39984*vY^4-vY^2*(39592*uY^2+39592)+9801=0 :=
  field_relation 1 0

 theorem Y_differential_relation :
    YFu uY vY • KaehlerDifferential.D K field uY+
      YFv uY vY • KaehlerDifferential.D K field vY=0 := by
  have hc (n:ℕ) [n.AtLeastTwo] : KaehlerDifferential.D K field (OfNat.ofNat n)=0 :=
    (KaehlerDifferential.D K field).map_natCast n
  have h := congrArg (KaehlerDifferential.D K field) Y_polynomial_relation
  simp only [map_add,map_sub,Derivation.leibniz,Derivation.leibniz_pow,hc,map_zero] at h
  unfold YFu YFv
  convert h using 1 <;> module

 theorem Z_differential_relation :
    ZFx x y • KaehlerDifferential.D K field x+
      ZFy x y • KaehlerDifferential.D K field y=0 :=
  ThetaDFiniteDifferential.differential_relation

/-- Actual chart equations of the original affine/vertical projective lines. -/
def affineFunction (α β : K) : field :=
  vY-algebraMap K field α*uY-algebraMap K field β

def verticalFunction (t : K) : field := x-algebraMap K field t*y

 theorem D_affineFunction (α β : K) :
    KaehlerDifferential.D K field (affineFunction α β)=
      KaehlerDifferential.D K field vY-algebraMap K field α • KaehlerDifferential.D K field uY := by
  simp [affineFunction,Derivation.leibniz,Derivation.map_algebraMap]

 theorem D_verticalFunction (t : K) :
    KaehlerDifferential.D K field (verticalFunction t)=
      KaehlerDifferential.D K field x-algebraMap K field t • KaehlerDifferential.D K field y := by
  simp [verticalFunction,Derivation.leibniz,Derivation.map_algebraMap]

 theorem affine_derivative_normal_form (α β : K) (hQ : YFv uY vY≠0) :
    KaehlerDifferential.D K field (affineFunction α β)=
      (-(YFu uY vY+algebraMap K field α*YFv uY vY)/YFv uY vY) •
        KaehlerDifferential.D K field uY := by
  have he : YFv uY vY • KaehlerDifferential.D K field vY=
      -(YFu uY vY • KaehlerDifferential.D K field uY) :=
    eq_neg_of_add_eq_zero_right Y_differential_relation
  have hh := congrArg (fun z : Ω[field⁄K] => (YFv uY vY)⁻¹ • z) he
  have hv : KaehlerDifferential.D K field vY=
      (-(YFv uY vY)⁻¹*YFu uY vY) • KaehlerDifferential.D K field uY := by
    simpa only [smul_smul,inv_mul_cancel₀ hQ,one_smul,smul_neg,neg_smul,neg_mul] using hh
  rw [D_affineFunction,hv,←sub_smul]
  congr 1
  field_simp
  ring

 theorem vertical_derivative_normal_form (t : K) (hP : ZFx x y≠0) :
    KaehlerDifferential.D K field (verticalFunction t)=
      (-(ZFy x y+algebraMap K field t*ZFx x y)/ZFx x y) •
        KaehlerDifferential.D K field y := by
  have he : ZFx x y • KaehlerDifferential.D K field x=
      -(ZFy x y • KaehlerDifferential.D K field y) :=
    eq_neg_of_add_eq_zero_left Z_differential_relation
  have hh := congrArg (fun z : Ω[field⁄K] => (ZFx x y)⁻¹ • z) he
  have hx : KaehlerDifferential.D K field x=
      (-(ZFx x y)⁻¹*ZFy x y) • KaehlerDifferential.D K field y := by
    simpa only [smul_smul,inv_mul_cancel₀ hP,one_smul,smul_neg,neg_smul,neg_mul] using hh
  rw [D_verticalFunction,hx,←sub_smul]
  congr 1
  field_simp
  ring

 theorem y_ne_zero : y≠0 := by
  intro hy
  have hh := linear_form_zero 0 0 1 (by simp [hy])
  exact one_ne_zero hh.2.2

 theorem affineFunction_times_y (α β : K) :
    affineFunction α β*y=1-algebraMap K field α*x-algebraMap K field β*y := by
  unfold affineFunction
  rw [YZ_transition.1,YZ_transition.2]
  field_simp [y_ne_zero]

 theorem affineFunction_ne_zero (α β : K) : affineFunction α β≠0 := by
  intro hz
  have he := affineFunction_times_y α β
  rw [hz,zero_mul] at he
  have hh := linear_form_zero 1 (-α) (-β) (by
    simp only [map_one,map_neg]
    linear_combination -he)
  exact one_ne_zero hh.1

 theorem verticalFunction_ne_zero (t : K) : verticalFunction t≠0 := by
  intro hz
  have hh := linear_form_zero 0 1 (-t) (by
    simp only [map_zero,map_one,map_neg,zero_add,one_mul]
    simpa only [verticalFunction,sub_eq_add_neg,neg_mul] using hz)
  exact one_ne_zero hh.2.1

/-- The SAME true global Kähler sheaf section has the actual line equation
as its native germ. This uses ONLY the NEW natural global bridge. -/
def affineGlobalSection (α β : K) : Γ(toBase.kaehler,⊤) :=
  ThetaDNaturalGlobalDifferentials.planeGlobalSectionEquiv
    (dotProductEquiv K (Fin 3) ![-α,-β,1])

def verticalGlobalSection (t : K) : Γ(toBase.kaehler,⊤) :=
  ThetaDNaturalGlobalDifferentials.planeGlobalSectionEquiv
    (dotProductEquiv K (Fin 3) ![1,-t,0])

 theorem affineGlobalSection_germ (α β : K) :
    ThetaDNaturalGlobalDifferentials.genericGerm (affineGlobalSection α β)=
      affineFunction α β • (y • omega) := by
  rw [affineGlobalSection,ThetaDNaturalGlobalDifferentials.actual_global_line_germ]
  rw [smul_smul,affineFunction_times_y]
  congr 1
  change algebraMap K field (1:K)+algebraMap K field (-α)*x+algebraMap K field (-β)*y=
    1-algebraMap K field α*x-algebraMap K field β*y
  simp only [map_one,map_neg]
  ring

 theorem verticalGlobalSection_germ (t : K) :
    ThetaDNaturalGlobalDifferentials.genericGerm (verticalGlobalSection t)=verticalFunction t • omega := by
  rw [verticalGlobalSection,ThetaDNaturalGlobalDifferentials.actual_global_line_germ]
  congr 1
  simp [verticalFunction,sub_eq_add_neg]

#print axioms Y_differential_relation
#print axioms affine_derivative_normal_form
#print axioms vertical_derivative_normal_form
#print axioms affineFunction_ne_zero
#print axioms verticalFunction_ne_zero
#print axioms affineGlobalSection_germ
#print axioms verticalGlobalSection_germ
end
end FourCorner.ThetaActualLineDifferentials
