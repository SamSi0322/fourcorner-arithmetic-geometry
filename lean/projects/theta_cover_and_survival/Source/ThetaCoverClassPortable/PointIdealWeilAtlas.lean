import ThetaCoverClassPortable.IdealMeromorphicAtlas
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_ord_eq_of_ker_pow_ideal_eq_span
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory TopologicalSpace
namespace FourCorner.PointIdealWeilAtlas
open SmoothProperClosedPointPlaces
attribute [local instance] Classical.propDecidable
variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
    (c : X ⟶ Spec (.of k)) [IsSeparated c] [SmoothOfRelativeDimension 1 c] [IsProper c]
    (P : Spec (.of k) ⟶ X) (hP : P≫c=𝟙 _)

include c hP in
lemma cartier : P.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id P hP
abbrev U : X → X.Opens := IdealMeromorphicAtlas.U P.ker (cartier c P hP)
abbrev q : X → X.functionField := IdealMeromorphicAtlas.q P.ker (cartier c P hP)

/-- The literal point-kernel ideal's true meromorphic module frame has
order one at that same point and zero at every other actual closed point. -/
theorem point_generator_order (x : closedPoints X) (i : X) (hx : x.val∈U c P hP i) :
    letI := fieldAlgebra c
    (placeOfClosedPoint c x).ord (q c P hP i)=if P (IsLocalRing.closedPoint k)=x.val then 1 else 0 := by
  letI := fieldAlgebra c
  let G := IdealMeromorphicAtlas.generator P.ker (cartier c P hP) i
  have hg : (P.ker^1).ideal G.U=Ideal.span {G.g} := by simpa only [pow_one] using G.ideal
  have hh := Scheme.Hom.ord_eq_of_ker_pow_ideal_eq_span c P hP 1 G.U G.U.property G.g hg
    x.val hx x.property (placeOfClosedPoint c x) (range_stalk c x)
  by_cases he : P (IsLocalRing.closedPoint k)=x.val
  · rw [if_pos he]
    exact hh.1 he
  · rw [if_neg he]
    exact hh.2 he

#print axioms point_generator_order
end FourCorner.PointIdealWeilAtlas
