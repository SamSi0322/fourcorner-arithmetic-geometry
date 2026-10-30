import ThetaCoverClassPortable.ThetaQuadraticField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial

namespace FourCorner.ThetaQuadraticContactAlgebra
open ThetaQuadraticCurve

theorem rational_parameter_nonsquare : ¬ IsSquare (2/99 : ℚ) := by norm_num
theorem rational_half_parameter_nonsquare : ¬ IsSquare (1/99 : ℚ) := by norm_num

/-- The contact ordinate does NOT lie in the quadratic coefficient field. -/
theorem parameter_not_square (z : F) : z^2 ≠ 2/99 := by
  intro h
  have hre := congrArg QuadraticAlgebra.re h
  have him := congrArg QuadraticAlgebra.im h
  norm_num [pow_two,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat,QuadraticAlgebra.norm_def] at hre him
  have hz : z.re*z.im=0 := by linarith
  rcases mul_eq_zero.mp hz with hr | hi
  · have hs : z.im^2=(1/99:ℚ) := by rw [hr] at hre; nlinarith [hre]
    exact rational_half_parameter_nonsquare ⟨z.im, by simpa only [pow_two] using hs.symm⟩
  · have hs : z.re^2=(2/99:ℚ) := by rw [hi] at hre; nlinarith [hre]
    exact rational_parameter_nonsquare ⟨z.re, by simpa only [pow_two] using hs.symm⟩

abbrev contactField := QuadraticAlgebra F (2/99) 0
instance contactIrreducible : Fact (∀ z : F, z^2 ≠ 2/99+0*z) :=
  ⟨fun z => by simpa using parameter_not_square z⟩

theorem contact_degree : Module.finrank F contactField=2 :=
  QuadraticAlgebra.finrank_eq_two _ _

def ordinate : contactField := QuadraticAlgebra.omega
def radical : contactField := algebraMap F contactField QuadraticAlgebra.omega
def abscissa (plus : Bool) : contactField := if plus then -radical else radical

theorem ordinate_sq : ordinate^2=(2/99:contactField) := by
  unfold ordinate
  rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp only [map_zero,zero_mul,add_zero,map_div₀,map_ofNat]
theorem radical_sq : radical^2=(2:contactField) := by
  unfold radical
  rw [←map_pow]
  have hh : (QuadraticAlgebra.omega:F)^2=2 := by
    rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  rw [hh,map_ofNat]
theorem abscissa_sq (plus : Bool) : abscissa plus^2=(2:contactField) := by
  cases plus <;> simp [abscissa,radical_sq]

/-- Literal restriction of the original quartic; contact multiplicity is
recorded as a polynomial identity, not yet as a curve valuation order. -/
theorem quartic_restriction (plus : Bool) (Y : contactField) :
    9801*(abscissa plus)^4+19598*(abscissa plus)^2*Y^2-39592*(abscissa plus)^2+
      9801*Y^4-39592*Y^2+39984=(99*Y^2-2)^2 := by
  rw [show (abscissa plus)^4=((abscissa plus)^2)^2 by ring,abscissa_sq]
  ring

def values (plus : Bool) : Fin 2 → contactField := ![abscissa plus,ordinate]

theorem chart_relations (plus : Bool) (a : Fin 1) :
    MvPolynomial.aeval (values plus) (ThetaDGeometricChartPoints.equation 2 a)=0 := by
  have hq : 9801*(abscissa plus)^4+19598*(abscissa plus)^2*ordinate^2-
      39592*(abscissa plus)^2+9801*ordinate^4-39592*ordinate^2+39984=0 := by
    rw [quartic_restriction,ordinate_sq]
    norm_num
  fin_cases a
  norm_num [ThetaDGeometricChartPoints.equation,ThetaQuotientChart.affineEquation,
    ThetaAmbientChart.dehom,ThetaLiteralModels.targetEquation,ThetaLiteralModels.targetPolynomial,
    ThetaTargetSmooth.drop_table,Fin.isValue,values]
  simp
  linear_combination hq

/-- A genuine map out of the original rational chart quotient. -/
def chartEvaluation (plus : Bool) : ThetaDPlaneChartSections.chartRing 2 →ₐ[ℚ] contactField :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (values plus)) (by
    have hh : ThetaQuotientChart.affineIdeal (ThetaLiteralModels.targetEquation ℚ) 2 ≤
        RingHom.ker (MvPolynomial.aeval (values plus)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      exact chart_relations plus a
    exact fun z hz=>hh hz)

@[simp] theorem chartEvaluation_X (plus : Bool) (a : Fin 2) :
    chartEvaluation plus (Ideal.Quotient.mk _ (X a))=values plus a :=
  MvPolynomial.aeval_X _ _

def rationalChartPoint (plus : Bool) : Spec (.of contactField) ⟶ ThetaLiteralModels.D ℚ :=
  Spec.map (CommRingCat.ofHom (chartEvaluation plus).toRingHom) ≫
    ThetaDPlaneChartSections.chartMap 2

abbrev pointToBase : Spec (.of contactField) ⟶ Spec (.of F) :=
  Scheme.TwoAffineOpenCover.specMap F contactField

/-- The ACTUAL closed quadratic contact candidate on the SAME D_F.
The field degree above is two; no two rational F-points are postulated. -/
def contactMap (plus : Bool) : Spec (.of contactField) ⟶ curve :=
  pullback.lift (rationalChartPoint plus) pointToBase
    (ThetaSourceComparison.rational_base_unique _ _)

@[reassoc (attr := simp)] theorem contactMap_toBase (plus : Bool) :
    contactMap plus ≫ toBase=pointToBase := by simp [contactMap,toBase]
@[reassoc (attr := simp)] theorem contactMap_toRational (plus : Bool) :
    contactMap plus ≫ toRational=rationalChartPoint plus := by simp [contactMap,toRational]

end FourCorner.ThetaQuadraticContactAlgebra
