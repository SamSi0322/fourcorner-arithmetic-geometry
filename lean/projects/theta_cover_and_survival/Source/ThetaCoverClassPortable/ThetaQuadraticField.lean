import ThetaCoverClassPortable.ThetaQuadraticCurve
import ThetaCoverClassPortable.NativeFunctionFieldFunctor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct

namespace FourCorner.ThetaQuadraticField
open ThetaQuadraticCurve ThetaNativeFunctionFieldMap
local instance : IsIntegral curve := curve_integral
local instance : IsIntegral ThetaDGeometricModel.geometricD := ThetaDGeometricModel.geometric_integral
local instance : IsIntegral (ThetaLiteralModels.D ℚ) := ThetaDPlaneChartSections.original_integral
local instance : Surjective geometricProjection := geometricProjection_surjective
local instance : Surjective toRational := toRational_surjective
local instance : Surjective ThetaDGeometricModel.qb := ThetaDChartNaturality.qb_surjective
local instance : Surjective (pullback.fst (ThetaLiteralModels.dToBase ℚ) ThetaDGeometricModel.qb) := inferInstance
local instance : Algebra F functionField := fieldAlgebra

/-- The actual generic-stalk map, not a chosen function-field embedding. -/
abbrev toGeometric : functionField →+* ThetaDGeometricModel.field :=
  fieldMap geometricProjection
abbrev fromRational : ThetaCoverRationalData.rationalField →+* functionField :=
  fieldMap toRational

theorem toGeometric_injective : Function.Injective toGeometric := toGeometric.injective

theorem generic_diagram :
    Spec.map (CommRingCat.ofHom toGeometric) ≫ curve.fromSpecStalk (genericPoint curve) =
      ThetaDGeometricModel.geometricD.fromSpecStalk (genericPoint ThetaDGeometricModel.geometricD) ≫
        geometricProjection := ThetaNativeFunctionFieldMap.generic_diagram _

theorem rational_composition : toGeometric.comp fromRational =
    fieldMap (pullback.fst (ThetaLiteralModels.dToBase ℚ) ThetaDGeometricModel.qb) := by
  simpa only [geometricProjection_toRational] using
    (NativeFunctionFieldFunctor.fieldMap_comp geometricProjection toRational).symm

/-- Scalar compatibility across the two DIFFERENT constant fields is derived
from the actual base Spec square and the generic Spec square. -/
theorem scalar_compatibility (a : F) :
    toGeometric (algebraMap F functionField a) =
      ThetaDGeometricModel.fieldAlgebra.algebraMap (coefficientEmbedding a) := by
  have h : CommRingCat.ofHom (toGeometric.comp (baseToFunctionField toBase)) =
      CommRingCat.ofHom ((baseToFunctionField ThetaDGeometricModel.toBase).comp
        coefficientEmbedding.toRingHom) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp]
    change Spec.map (CommRingCat.ofHom toGeometric) ≫
        Spec.map (CommRingCat.ofHom (SmoothCurveExtension.baseMap toBase)) = _
    rw [← SmoothCurveExtension.generic_comp_to_base toBase, ← Category.assoc,
      ThetaNativeFunctionFieldMap.generic_diagram, Category.assoc,
      geometricProjection_toBase, ← Category.assoc,
      SmoothCurveExtension.generic_comp_to_base]
    rfl
  exact congrArg (fun f => f.hom a) h

abbrev chartOpen (j : Fin 3) : curve.Opens := toRational ⁻¹ᵁ ThetaDPlaneChartSections.U j

theorem chartOpen_affine (j : Fin 3) : IsAffineOpen (chartOpen j) := by
  let e := P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.pullbackAffineOpenIsoSpecTensor
    (ThetaLiteralModels.dToBase ℚ) F (ThetaDPlaneChartSections.U j)
      (ThetaDPlaneChartSections.affine_U j)
  exact IsAffine.of_isIso e.hom

theorem chartOpen_nonempty (j : Fin 3) : Nonempty (chartOpen j) := by
  obtain ⟨p⟩ := ThetaDChartNaturality.U_nonempty j
  obtain ⟨q,hq⟩ := toRational.surjective p.val
  exact ⟨⟨q,by simpa [chartOpen,hq] using p.property⟩⟩

local instance (j : Fin 3) : Nonempty (chartOpen j) := chartOpen_nonempty j
local instance (j : Fin 3) : Nonempty (ThetaDPlaneChartSections.U j) := ThetaDChartNaturality.U_nonempty j

/-- Coordinates are germs of sections on the ACTUAL dense affine opens. -/
def coordinate (j : Fin 3) (a : Fin 2) : functionField :=
  curve.germToFunctionField (chartOpen j)
    ((toRational.app (ThetaDPlaneChartSections.U j)).hom
      ((ThetaDPlaneChartSections.sectionsRingEquiv j).symm
        (Ideal.Quotient.mk _ (X a))))

theorem coordinate_eq_rational_ratio (j : Fin 3) (a : Fin 2) :
    coordinate j a = fromRational
      (ThetaDNativeProjRatios.ratio j (ThetaAmbientChart.insert 2 j a)) := by
  rw [coordinate, ← ThetaDChartNaturality.generic_germ_naturality toRational]
  change fromRational ((ThetaLiteralModels.D ℚ).germToFunctionField
    (ThetaDPlaneChartSections.U j)
      ((ThetaDPlaneChartSections.sectionsRingEquiv j).symm (Ideal.Quotient.mk _ (X a)))) = _
  rw [ThetaDSectionComparison.original_section_comparison,
    ThetaDNativeProjSections.sections_coordinate_generic]

theorem coordinate_image (j : Fin 3) (a : Fin 2) :
    toGeometric (coordinate j a) = ThetaDFieldCoordinates.coordinate j a := by
  rw [coordinate_eq_rational_ratio, ← RingHom.comp_apply, rational_composition]
  exact (ThetaDExactChartTransitions.coordinate_eq_native_ratio j a).symm

abbrev x2 := coordinate 2 0
abbrev y2 := coordinate 2 1
def r2 : functionField := algebraMap F functionField QuadraticAlgebra.omega
/-- Pullback of the literal rational h along the actual rational projection. -/
def h2 : functionField := fromRational ThetaCoverRationalData.rationalH
def numerator2 : functionField := 97*x2^2+99*y2^2-196
def ellPlus2 : functionField := 1+x2/r2
def ellMinus2 : functionField := 1-x2/r2
def squareMultiplier2 : functionField := numerator2/(28*r2*ellPlus2)

theorem r2_image : toGeometric r2 = ThetaCoverFunctions.radical := by
  exact scalar_compatibility _
theorem h2_image : toGeometric h2 = ThetaCoverFunctions.h := by
  change toGeometric (fromRational _) = _
  rw [← RingHom.comp_apply, rational_composition]
  exact ThetaCoverRationalData.rationalH_image

theorem h2_formula : h2=(x2^2+y2^2-2)/2 := by
  unfold h2 ThetaCoverRationalData.rationalH
  simp only [map_div₀,map_sub,map_add,map_pow,map_ofNat]
  simp only [x2,y2,coordinate_eq_rational_ratio]
  rfl

theorem numerator2_image : toGeometric numerator2 = ThetaCoverFunctions.numerator := by
  simp only [numerator2,ThetaCoverFunctions.numerator,map_sub,map_add,map_mul,map_pow,map_ofNat,
    coordinate_image]
theorem ellPlus2_image : toGeometric ellPlus2 = ThetaCoverFunctions.ellPlus := by
  simp only [ellPlus2,ThetaCoverFunctions.ellPlus,map_add,map_one,map_div₀,coordinate_image,r2_image]
theorem ellMinus2_image : toGeometric ellMinus2 = ThetaCoverFunctions.ellMinus := by
  simp only [ellMinus2,ThetaCoverFunctions.ellMinus,map_sub,map_one,map_div₀,coordinate_image,r2_image]
theorem squareMultiplier2_image :
    toGeometric squareMultiplier2 = ThetaCoverFunctions.squareMultiplier := by
  simp only [squareMultiplier2,ThetaCoverFunctions.squareMultiplier,map_div₀,map_mul,map_ofNat,
    numerator2_image,r2_image,ellPlus2_image]

theorem r2_sq : r2^2=2 := by
  apply toGeometric_injective
  simpa only [map_pow,map_ofNat,r2_image] using ThetaCoverFunctions.radical_sq
theorem r2_ne_zero : r2≠0 := by
  intro h
  exact ThetaCoverFunctions.radical_ne_zero (by rw [←r2_image,h,map_zero])
theorem h2_ne_zero : h2≠0 := by
  intro h
  exact ThetaCoverFunctions.h_ne_zero (by rw [←h2_image,h,map_zero])
theorem ellPlus2_ne_zero : ellPlus2≠0 := by
  intro h
  exact ThetaCoverFunctions.ellPlus_ne_zero (by rw [←ellPlus2_image,h,map_zero])
theorem ellMinus2_ne_zero : ellMinus2≠0 := by
  intro h
  exact ThetaCoverFunctions.ellMinus_ne_zero (by rw [←ellMinus2_image,h,map_zero])

/-- Exact identity IN F(D_F), including its scalar 28*r2 and denominators. -/
theorem exact_quadratic_identity : h2=(ellPlus2/ellMinus2)*squareMultiplier2^2 := by
  apply toGeometric_injective
  simpa only [map_mul,map_div₀,map_pow,h2_image,ellPlus2_image,ellMinus2_image,
    squareMultiplier2_image] using ThetaCoverFunctions.exact_cover_identity

end FourCorner.ThetaQuadraticField
