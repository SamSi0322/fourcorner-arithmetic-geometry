import ThetaCoverClassPortable.ThetaQQUnitRootOpens
import ThetaCoverClassPortable.KummerSquareLine

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
namespace FourCorner.ThetaQQKummerLine
open ThetaLiteralModels ThetaCoverRationalData ThetaQQUnitRootOpens
local instance : IsIntegral (D ℚ) := ThetaDPlaneChartSections.original_integral
local instance : SmoothOfRelativeDimension 1 (dToBase ℚ) := ThetaTargetSmooth.target_smooth

def units (i : NonemptyIndex) : Γ(D ℚ,W i)ˣ := localUnit i.val
def roots (i : NonemptyIndex) : (D ℚ).functionField := root i.val

theorem units_square (i : NonemptyIndex) :
    algebraMap Γ(D ℚ,W i) (D ℚ).functionField (units i:Γ(D ℚ,W i))=roots i^2*rationalH := localUnit_square i.val

def transitionCocycle : UnitCocycle W := KummerUnitCocycle.cocycle
  (dToBase ℚ) W affine_inf rationalH roots units units_square

/-- An actual invertible structure-sheaf module on the ORIGINAL D/QQ,
constructed from original cover coefficients and actual regular units. -/
def L : (D ℚ).Modules := glueOfCocycle transitionCocycle

theorem L_invertible : Scheme.Modules.IsInvertible L := isInvertible_glueOfCocycle nonempty_cover transitionCocycle

theorem transition_native_field (i j : NonemptyIndex) :
    letI : Nonempty ((W i ⊓ W j : (D ℚ).Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _
    algebraMap Γ(D ℚ,W i ⊓ W j) (D ℚ).functionField (transitionCocycle.u i j)=roots j/roots i := by
  exact KummerUnitCocycle.transition_field (dToBase ℚ) W affine_inf rationalH roots units units_square i j

theorem square_trivialization :
    ∃e : (L ⊗ L) ≅ 𝟙_ (D ℚ).Modules,
      ∀i,e.hom.app (W i) (tensorSections (glueFrame transitionCocycle i) (glueFrame transitionCocycle i))=
        (units i:Γ(D ℚ,W i)) • unitSection (W i) :=
  KummerSquareLine.exists_square_trivialization (dToBase ℚ) W affine_inf rationalH roots units units_square nonempty_cover

#print axioms L_invertible
#print axioms square_trivialization
end FourCorner.ThetaQQKummerLine
