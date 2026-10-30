import ThetaCoverClassPortable.ThetaGeometricResidueCoordinates

namespace FourCorner.ThetaContactTangencyCertificates
open AlgebraicGeometry AlgebraicCurve Polynomial MvPolynomial
open ThetaDGeometricModel ThetaGeometricContactPoints ThetaLinesPolynomialContacts
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Literal partials, over arbitrary commutative rings so they can also be
used INSIDE the actual valuation rings and their residue maps. -/
def YFu {R : Type*} [CommRing R] (a b : R) : R := a*(39204*a^2-79184*b^2+39196)
def YFv {R : Type*} [CommRing R] (a b : R) : R := b*(159936*b^2-79184*a^2-79184)
def ZFx {R : Type*} [CommRing R] (a b : R) : R := a*(39204*a^2+39196*b^2-79184)
def ZFy {R : Type*} [CommRing R] (a b : R) : R := b*(39196*a^2+39204*b^2-79184)

 theorem affine_derivative (α β z : K) :
    (affineRestriction α β).derivative.eval z=YFu z (α*z+β)+α*YFv z (α*z+β) := by
  simp [affineRestriction,thetaF,YFu,YFv,Polynomial.derivative_add,Polynomial.derivative_sub,
    Polynomial.derivative_mul,Polynomial.derivative_pow]
  ring

 theorem vertical_derivative (t z : K) :
    (verticalRestriction t).derivative.eval z=t*ZFx (t*z) z+ZFy (t*z) z := by
  simp [verticalRestriction,thetaF,ZFx,ZFy,Polynomial.derivative_add,Polynomial.derivative_sub,
    Polynomial.derivative_mul,Polynomial.derivative_pow]
  ring

 theorem factored_derivative_zero (c x y : K) :
    (Polynomial.C c*(Polynomial.X-Polynomial.C x)^2*(Polynomial.X-Polynomial.C y)^2).derivative.eval x=0 := by
  simp [Polynomial.derivative_mul,Polynomial.derivative_pow]

 theorem affine_gradient (α β z : K) (hz : thetaF z 1 (α*z+β)=0) :
    YFu z (α*z+β)≠0 ∨ YFv z (α*z+β)≠0 := by
  let e := ThetaDGeometricChartPoints.evaluation 1 ![z,α*z+β] (affine_relations α β z hz)
  obtain ⟨i,hi⟩ := ThetaTargetSmooth.field_jacobian (k:=ℚ) 1 K e
  rw [ThetaTargetSmooth.jacobian_formula] at hi
  have he (a : Fin 2) : e (ThetaTargetSmooth.ax 1 a)=![z,α*z+β] a := MvPolynomial.aeval_X _ _
  simp only [he] at hi
  fin_cases i
  · left;convert hi using 1 <;> simp [ThetaTargetSmooth.minorScalar,YFu] <;> ring
  · right;convert hi using 1 <;> simp [ThetaTargetSmooth.minorScalar,YFv] <;> ring

 theorem vertical_gradient (t z : K) (hz : thetaF (t*z) z 1=0) :
    ZFx (t*z) z≠0 ∨ ZFy (t*z) z≠0 := by
  have hh := ThetaDFiniteDifferential.gradient_nonzero (t*z) z (by
    unfold thetaF at hz
    linear_combination hz)
  exact hh

/-- A double root of the literal affine restriction has a NONZERO normal
partial and zero actual tangent derivative. No normal-unit premise is assumed. -/
theorem affine_normal_and_tangent (α β z : K) (hz : thetaF z 1 (α*z+β)=0)
    (hd : (affineRestriction α β).derivative.eval z=0) :
    YFv z (α*z+β)≠0 ∧ YFu z (α*z+β)+α*YFv z (α*z+β)=0 := by
  have ht : YFu z (α*z+β)+α*YFv z (α*z+β)=0 := by rw [←affine_derivative];exact hd
  refine ⟨?_,ht⟩
  intro hq
  have hp : YFu z (α*z+β)=0 := by simpa only [hq,mul_zero,add_zero] using ht
  exact (affine_gradient α β z hz).elim (fun h=>h hp) (fun h=>h hq)

 theorem vertical_normal_and_tangent (t z : K) (hz : thetaF (t*z) z 1=0)
    (hd : (verticalRestriction t).derivative.eval z=0) :
    ZFx (t*z) z≠0 ∧ t*ZFx (t*z) z+ZFy (t*z) z=0 := by
  have ht : t*ZFx (t*z) z+ZFy (t*z) z=0 := by rw [←vertical_derivative];exact hd
  refine ⟨?_,ht⟩
  intro hq
  have hp : ZFy (t*z) z=0 := by simpa only [hq,mul_zero,zero_add] using ht
  exact (vertical_gradient t z hz).elim (fun h=>h hq) (fun h=>h hp)

#print axioms affine_derivative
#print axioms vertical_derivative
#print axioms affine_gradient
#print axioms affine_normal_and_tangent
#print axioms vertical_normal_and_tangent
end
end FourCorner.ThetaContactTangencyCertificates
