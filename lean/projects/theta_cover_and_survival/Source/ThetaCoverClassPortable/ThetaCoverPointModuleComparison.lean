import ThetaCoverClassPortable.ThetaActualPointPairs
import ThetaCoverClassPortable.MeromorphicComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
namespace FourCorner.ThetaCoverPointModuleComparison
open ThetaDGeometricModel SmoothProperClosedPointPlaces MeromorphicFrames
local instance : IsIntegral (ThetaLiteralModels.D ℚ) := ThetaDPlaneChartSections.original_integral
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := ThetaDGeometricModel.fieldAlgebra
local instance : IsAffineHom ThetaGeometricKummerLine.projection := by
  dsimp [ThetaGeometricKummerLine.projection]
  letI := isAffineHom_isStableUnderBaseChange
  exact MorphismProperty.pullback_fst _ _ (isAffineHom_of_isAffine qb)

lemma affine_V (i : ThetaQQUnitRootOpens.NonemptyIndex) : IsAffineOpen (ThetaGeometricKummerLine.V i) :=
  (ThetaQQUnitRootOpens.affine_U i.val).preimage ThetaGeometricKummerLine.projection

abbrev coverAtlas : Atlas (glueOfCocycle ThetaGeometricKummerLine.cc) :=
  Atlas.ofGlue ThetaGeometricKummerLine.V ThetaGeometricKummerLine.cover affine_V
    ThetaGeometricKummerLine.cc ThetaGeometricKummerLine.roots ThetaGeometricKummerLine.root_ne_zero
    ThetaGeometricKummerLine.transition_field

abbrev pointAtlas : Atlas (PointPairTensorFamily.tensorModule toBase ThetaActualPointPairs.actualPairs) :=
  PointPairTensorFamily.tensorAtlas toBase ThetaActualPointPairs.actualPairs

/-- A REAL sheaf isomorphism between the true geometric pullback of the
QQ cover line and the tensor of the eight actual E/infinity point-kernel
modules. Equal Weil data is converted through actual regular units. -/
theorem actual_module_iso : Nonempty (ThetaGeometricKummerLine.L ≅
    PointPairTensorFamily.tensorModule toBase ThetaActualPointPairs.actualPairs) := by
  obtain ⟨g,_⟩ := ThetaGeometricKummerLine.actual_pullback_glue
  have hi : Nonempty (glueOfCocycle ThetaGeometricKummerLine.cc ≅
      PointPairTensorFamily.tensorModule toBase ThetaActualPointPairs.actualPairs) :=
    Atlas.nonempty_iso_of_equal_orders coverAtlas pointAtlas toBase (by
      intro x i j hx
      have hl := ThetaKummerWeilComparison.actual_Weil_order x i hx.1
      rw [ThetaKummerWeilComparison.localEquation,Place.ord_inv] at hl
      have hr := PointPairTensorFamily.tensor_order toBase x ThetaActualPointPairs.actualPairs j hx.2
      rw [ThetaActualPointPairs.order_sum] at hr
      simp only [Finsupp.sub_apply] at hl
      change (placeOfClosedPoint toBase x).ord (pointAtlas.q j)=_ at hr
      change (placeOfClosedPoint toBase x).ord (ThetaGeometricKummerLine.roots i)=
        (placeOfClosedPoint toBase x).ord (pointAtlas.q j)
      omega)
  exact ⟨g ≪≫ hi.some⟩

#print axioms actual_module_iso
end FourCorner.ThetaCoverPointModuleComparison
