import ThetaCoverClassPortable.MeromorphicTensor
import ThetaCoverClassPortable.MeromorphicDual
import ThetaCoverClassPortable.MeromorphicUnit
import ThetaCoverClassPortable.PointIdealWeilAtlas
import ThetaCoverClassPortable.PointKernelPairAlgEquiv

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace NeronModelInfra
open AlgebraicGeometry.Scheme.Modules
namespace FourCorner.PointPairTensorFamily
open MeromorphicFrames SmoothProperClosedPointPlaces
attribute [local instance] Classical.propDecidable
variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
    (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
abbrev Point := SchemeHomOver (𝟙 (Spec (.of k))) c
abbrev Pair := Point c × Point c
abbrev pairModule (p : Pair c) : X.Modules := p.1.val.ker.invModule ⊗ p.2.val.ker.module

abbrev pairAtlas (p : Pair c) : Atlas (pairModule c p) :=
  Atlas.tensor c (Atlas.dual (Atlas.ofIdeal p.1.val.ker (PointIdealWeilAtlas.cartier c p.1.val p.1.property)))
    (Atlas.ofIdeal p.2.val.ker (PointIdealWeilAtlas.cartier c p.2.val p.2.property))

def tensorModule : List (Pair c) → X.Modules
  | [] => 𝟙_ X.Modules
  | p::ps => pairModule c p ⊗ tensorModule ps

def tensorAtlas : (ps : List (Pair c)) → Atlas (tensorModule c ps)
  | [] => Atlas.unit X
  | p::ps => Atlas.tensor c (pairAtlas c p) (tensorAtlas ps)

def orderPair (x : closedPoints X) (p : Pair c) : ℤ :=
  -(if p.1.val (IsLocalRing.closedPoint k)=x.val then 1 else 0)+
    (if p.2.val (IsLocalRing.closedPoint k)=x.val then 1 else 0)

lemma pair_order (x : closedPoints X) (p : Pair c) (i : (pairAtlas c p).Index)
    (hx : x.val∈(pairAtlas c p).U i) :
    letI := fieldAlgebra c
    (placeOfClosedPoint c x).ord ((pairAtlas c p).q i)=orderPair c x p := by
  letI := fieldAlgebra c
  change (placeOfClosedPoint c x).ord
    ((IdealMeromorphicAtlas.q p.1.val.ker (PointIdealWeilAtlas.cartier c p.1.val p.1.property) i.1)⁻¹ *
      IdealMeromorphicAtlas.q p.2.val.ker (PointIdealWeilAtlas.cartier c p.2.val p.2.property) i.2)=_
  rw [(placeOfClosedPoint c x).ord_mul
    (inv_ne_zero (IdealMeromorphicAtlas.q_ne_zero _ _ i.1))
    (IdealMeromorphicAtlas.q_ne_zero _ _ i.2),Place.ord_inv,
    PointIdealWeilAtlas.point_generator_order c p.1.val p.1.property x i.1 hx.1,
    PointIdealWeilAtlas.point_generator_order c p.2.val p.2.property x i.2 hx.2]
  rfl

lemma tensor_order (x : closedPoints X) (ps : List (Pair c)) (i : (tensorAtlas c ps).Index)
    (hx : x.val∈(tensorAtlas c ps).U i) :
    letI := fieldAlgebra c
    (placeOfClosedPoint c x).ord ((tensorAtlas c ps).q i)=(ps.map (orderPair c x)).sum := by
  letI := fieldAlgebra c
  induction ps with
  | nil => exact (placeOfClosedPoint c x).ord_one
  | cons p ps ih =>
    change (placeOfClosedPoint c x).ord ((pairAtlas c p).q i.1*(tensorAtlas c ps).q i.2)=_
    rw [(placeOfClosedPoint c x).ord_mul ((pairAtlas c p).q_ne_zero i.1) ((tensorAtlas c ps).q_ne_zero i.2),
      pair_order c x p i.1 hx.1,ih i.2 hx.2]
    rfl

section AlgebraicEquivalence
variable [GeometricallyIntegral c] [LocallyOfFiniteType c]

theorem tensor_algEquivZero (ps : List (Pair c)) : RelPicard.IsAlgEquivZero c (tensorModule c ps) := by
  induction ps with
  | nil => exact RelPicard.IsAlgEquivZero.tensorUnit c
  | cons p ps ih => exact (PointKernelPairAlgEquiv.actual_point_pair c p.1 p.2).tensor ih

end AlgebraicEquivalence
#print axioms tensor_order
#print axioms tensor_algEquivZero
end FourCorner.PointPairTensorFamily
