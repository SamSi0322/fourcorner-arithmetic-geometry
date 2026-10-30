import ThetaCoverClassPortable.PointPairTensorFamily
import ThetaCoverClassPortable.ThetaQQCoverLineEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace NeronModelInfra
namespace FourCorner.ThetaActualPointPairs
open ThetaDGeometricModel SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces SchemePointStalkEvaluation
open PointPairTensorFamily
attribute [local instance] Classical.propDecidable
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra

def boundaryEnumeration : Fin 4 ≃ ThetaCoverBoundaryPoints.Signs :=
  (Fintype.equivFinOfCardEq (by decide : Fintype.card ThetaCoverBoundaryPoints.Signs=4)).symm

def infinityEnumeration : Fin 4 ≃ ThetaDFourInfinityPlaces.Parameters :=
  (Finset.equivFinOfCardEq ThetaDInfinityPoints.parameters_card).symm

def boundarySection (e : ThetaCoverBoundaryPoints.Signs) : Point toBase :=
  ⟨(ThetaCoverBoundaryPoints.point e).val,(ThetaCoverBoundaryPoints.point e).property⟩
def infinitySection (e : ThetaDFourInfinityPlaces.Parameters) : Point toBase :=
  ⟨(ThetaDFourInfinityPlaces.actualPoint e).val,(ThetaDFourInfinityPlaces.actualPoint e).property⟩

def pairEntry (i : Fin 4) : Pair toBase :=
  (boundarySection (boundaryEnumeration i),infinitySection (infinityEnumeration i))
def actualPairs : List (Pair toBase) := List.ofFn pairEntry

theorem point_center_iff_place (P : RationalPoint toBase) (x : closedPoints geometricD) :
    P.val (IsLocalRing.closedPoint K)=x.val ↔
      (pointEquivRationalPlace toBase P).val=placeOfClosedPoint toBase x := by
  change _ ↔ placeOfClosedPoint toBase (closedPointOfPoint toBase P.val P.property)=placeOfClosedPoint toBase x
  rw [(placeOfClosedPoint_injective toBase).eq_iff]
  constructor
  · intro he
    exact Subtype.ext he
  · intro he
    exact congrArg Subtype.val he

theorem infinitySum_eq : ThetaDCanonicalInfinityDivisor.infinitySum=
    ∑e : ThetaDFourInfinityPlaces.Parameters,Finsupp.single (ThetaDFourInfinityPlaces.place e) 1 := by
  unfold ThetaDCanonicalInfinityDivisor.infinitySum ThetaDCanonicalInfinityDivisor.infinityPlaces
  rw [Finset.sum_image]
  exact fun a _ b _ h=>ThetaDFourInfinityPlaces.place_injective h

theorem order_sum (x : closedPoints geometricD) :
    (actualPairs.map (orderPair toBase x)).sum=
      -(ThetaCoverBoundaryPoints.boundarySum (placeOfClosedPoint toBase x))+
        ThetaDCanonicalInfinityDivisor.infinitySum (placeOfClosedPoint toBase x) := by
  let w := placeOfClosedPoint toBase x
  have he : (∑i : Fin 4,if (boundarySection (boundaryEnumeration i)).val (IsLocalRing.closedPoint K)=x.val then (1:ℤ) else 0)=
      ThetaCoverBoundaryPoints.boundarySum w := by
    simp only [boundarySection]
    simp_rw [point_center_iff_place]
    change (∑i : Fin 4,if ThetaCoverBoundaryPoints.place (boundaryEnumeration i)=w then (1:ℤ) else 0)=_
    rw [boundaryEnumeration.sum_comp (fun e=>if ThetaCoverBoundaryPoints.place e=w then (1:ℤ) else 0)]
    simp only [ThetaCoverBoundaryPoints.boundarySum,Finsupp.finsetSum_apply,Finsupp.single_apply]
  have hh : (∑i : Fin 4,if (infinitySection (infinityEnumeration i)).val (IsLocalRing.closedPoint K)=x.val then (1:ℤ) else 0)=
      ThetaDCanonicalInfinityDivisor.infinitySum w := by
    simp only [infinitySection]
    simp_rw [point_center_iff_place]
    change (∑i : Fin 4,if ThetaDFourInfinityPlaces.place (infinityEnumeration i)=w then (1:ℤ) else 0)=_
    rw [infinityEnumeration.sum_comp (fun e=>if ThetaDFourInfinityPlaces.place e=w then (1:ℤ) else 0),infinitySum_eq]
    simp only [Finsupp.finsetSum_apply,Finsupp.single_apply]
  change (List.ofFn (fun i : Fin 4=>orderPair toBase x (pairEntry i))).sum=_
  rw [List.sum_ofFn]
  change (∑i : Fin 4, (-(if (boundarySection (boundaryEnumeration i)).val (IsLocalRing.closedPoint K)=x.val then (1:ℤ) else 0)+
    (if (infinitySection (infinityEnumeration i)).val (IsLocalRing.closedPoint K)=x.val then (1:ℤ) else 0)))=_
  rw [Finset.sum_add_distrib,Finset.sum_neg_distrib,he,hh]

#print axioms order_sum
end FourCorner.ThetaActualPointPairs
