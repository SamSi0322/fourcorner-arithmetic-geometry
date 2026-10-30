import ThetaCoverClassPortable.ThetaLinesFullAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaCoverFunctions
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDCanonicalPlaneBasis
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : CharZero field := charZero_of_injective_algebraMap (algebraMap K field).injective

/-- The literal C0/Z² on the actual original Z-chart function field. -/
def c0 : field := x^2+y^2-2
/-- The literal N/Z² on the same native function field. -/
def numerator : field := 97*x^2+99*y^2-196
/-- The literal cover equation h=C0/(2Z²), not a new labelled cover. -/
def h : field := c0/2
abbrev radical : field := algebraMap K field ThetaLinesAbsoluteGalois.r
def ellPlus : field := 1+x/radical
def ellMinus : field := 1-x/radical
def squareMultiplier : field := numerator/(28*radical*ellPlus)

theorem radical_sq : radical^2=2 := by
  change (algebraMap K field ThetaLinesAbsoluteGalois.r)^2=2
  rw [←map_pow,ThetaLinesAbsoluteGalois.r_sq,map_ofNat]
theorem radical_ne_zero : radical≠0 := by
  intro hz
  have hh:=radical_sq
  rw [hz,zero_pow (by decide)] at hh
  norm_num at hh

theorem conic_identity : numerator^2=784*c0*(1-x^2/2) := by
  unfold numerator c0
  linear_combination polynomial_relation

theorem elimination_identity : (x^2-y^2)^2+9800*c0^2-392*c0=0 := by
  unfold c0
  linear_combination polynomial_relation

theorem x_ne_constant (a : K) : x≠algebraMap K field a := by
  intro hx
  have he : algebraMap K field (-a)+algebraMap K field 1*x+algebraMap K field 0*y=0 := by simp [hx]
  have hh:=(linear_form_zero (-a) 1 0 he).2.1
  exact one_ne_zero hh

theorem c0_ne_zero : c0≠0 := by
  intro hz
  have he:=elimination_identity
  rw [hz] at he
  have hxy : x^2=y^2 := by
    have hh : (x^2-y^2)^2=0 := by simpa using he
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hh)
  have hx : x^2=1 := by
    unfold c0 at hz
    linear_combination (1/2)*hz+(1/2)*hxy
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp (show x^2=(1:field)^2 by simpa using hx)) with hh|hh
  · exact x_ne_constant 1 (by simpa using hh)
  · exact x_ne_constant (-1) (by simpa using hh)

theorem h_ne_zero : h≠0 := div_ne_zero c0_ne_zero (by norm_num)

theorem ellPlus_ne_zero : ellPlus≠0 := by
  intro hz
  have he : algebraMap K field 1+algebraMap K field (ThetaLinesAbsoluteGalois.r⁻¹)*x+
      algebraMap K field 0*y=0 := by
    rw [map_one,map_zero,zero_mul,add_zero,map_inv₀]
    change 1+radical⁻¹*x=0
    calc
      1+radical⁻¹*x=ellPlus := by unfold ellPlus;rw [div_eq_mul_inv];ring
      _=0 := hz
  exact one_ne_zero (linear_form_zero 1 _ 0 he).1

theorem ellMinus_ne_zero : ellMinus≠0 := by
  intro hz
  have he : algebraMap K field 1+algebraMap K field (-ThetaLinesAbsoluteGalois.r⁻¹)*x+
      algebraMap K field 0*y=0 := by
    rw [map_one,map_zero,zero_mul,add_zero,map_neg,map_inv₀]
    change 1+(-radical⁻¹)*x=0
    calc
      1+(-radical⁻¹)*x=ellMinus := by unfold ellMinus;rw [div_eq_mul_inv];ring
      _=0 := hz
  exact one_ne_zero (linear_form_zero 1 _ 0 he).1

theorem line_product : ellPlus*ellMinus=1-x^2/2 := by
  have hi : (radical⁻¹)^2=(1/2:field) := by
    rw [inv_pow,radical_sq]
    norm_num
  calc
    ellPlus*ellMinus=1-x^2*(radical⁻¹)^2 := by
      unfold ellPlus ellMinus
      rw [div_eq_mul_inv]
      ring
    _=1-x^2/2 := by rw [hi];ring

theorem numerator_ne_zero : numerator≠0 := by
  intro hz
  have he:=conic_identity
  rw [hz,zero_pow (by decide),←line_product] at he
  exact (mul_ne_zero (mul_ne_zero (by norm_num) c0_ne_zero)
    (mul_ne_zero ellPlus_ne_zero ellMinus_ne_zero)) he.symm

/-- Exact identity, including 28*sqrt(2) and BOTH line denominators, in the
native function field of the actual original D_Qbar. -/
theorem exact_cover_identity : h=(ellPlus/ellMinus)*squareMultiplier^2 := by
  unfold h squareMultiplier
  field_simp [ellPlus_ne_zero,ellMinus_ne_zero,radical_ne_zero]
  rw [radical_sq]
  have he:=conic_identity
  rw [←line_product] at he
  linear_combination -he

#print axioms exact_cover_identity
end FourCorner.ThetaCoverFunctions
