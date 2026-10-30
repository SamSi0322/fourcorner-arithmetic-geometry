import ThetaCoverClassPortable.ThetaQuadraticContactPlaces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits

namespace FourCorner.ThetaQuadraticBoundary
open ThetaQuadraticCurve SmoothProperRationalPointPlaces
local instance : IsIntegral curve := curve_integral
local instance : IsProper toBase := curve_proper
local instance : SmoothOfRelativeDimension 1 toBase := curve_smooth
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra
local instance : IsIntegral ThetaDGeometricModel.geometricD := ThetaDGeometricModel.geometric_integral

abbrev Signs := ThetaCoverBoundaryPoints.Signs

/-- Literal base change of the four original rational boundary points. -/
def point (e : Signs) : Spec (.of F) ⟶ curve :=
  pullback.lift (baseMap ≫ ThetaCoverRationalData.rationalPoint e) (𝟙 _) (by
    rw [Category.assoc,ThetaCoverRationalData.rationalPoint_over,Category.comp_id,Category.id_comp])

@[reassoc (attr := simp)] theorem point_over (e : Signs) : point e ≫ toBase=𝟙 _ := by
  simp [point,toBase]
@[reassoc (attr := simp)] theorem point_original (e : Signs) :
    point e ≫ toRational=baseMap ≫ ThetaCoverRationalData.rationalPoint e := by
  simp [point,toRational]

/-- Equality of the actual points in the actual quadratic pullback square. -/
theorem geometric_point_basechange (e : Signs) :
    (ThetaCoverBoundaryPoints.point e).val ≫ geometricProjection=extensionMap ≫ point e := by
  apply pullback.hom_ext
  · simp only [Category.assoc,geometricProjection_toRational,point_original]
    rw [←Category.assoc,extensionMap_comp]
    exact ThetaCoverRationalData.rationalPoint_basechange e
  · simp only [Category.assoc,geometricProjection_toBase,point_over,Category.comp_id]
    rw [←Category.assoc]
    change ((ThetaCoverBoundaryPoints.point e).val ≫ ThetaDGeometricModel.toBase) ≫ extensionMap=extensionMap
    rw [(ThetaCoverBoundaryPoints.point e).property,Category.id_comp]

def place (e : Signs) : Place F functionField :=
  (pointToRationalPlace toBase ⟨point e,point_over e⟩).val

theorem place_rational (e : Signs) : (place e).IsRational :=
  (pointToRationalPlace toBase ⟨point e,point_over e⟩).property

def residueEquiv (e : Signs) : F ≃ₐ[F] (place e).ResidueField :=
  AlgEquiv.ofBijective (Algebra.ofId F (place e).ResidueField)
    ⟨(algebraMap F (place e).ResidueField).injective,place_rational e⟩

theorem place_degree (e : Signs) : (place e).deg=1 := by
  change Module.finrank F (place e).ResidueField=1
  rw [←(residueEquiv e).toLinearEquiv.finrank_eq]
  exact Module.finrank_self F

/-- The actual four rational closed-point Weil cycles over F. -/
def E2 : Divisor F functionField := ∑e : Signs,Finsupp.single (place e) 1

theorem E2_effective : 0≤E2 := by
  classical
  intro w
  simp only [E2,Finsupp.finsetSum_apply,Finsupp.single_apply]
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem E2_degree : Divisor.degree E2=4 := by
  simp [E2,map_sum,Divisor.degree_single,place_degree]

end FourCorner.ThetaQuadraticBoundary
