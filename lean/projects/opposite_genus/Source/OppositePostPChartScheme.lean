import OppositePostPChart

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace FourCorner.OppositeProjective.PostPChart
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The actual P-basic-open scheme is the affine quotient of the P=1 equations,
with ordered affine coordinates T,Q,R,Z. -/
def chartSchemeIso (mu nu : K) :
    (Proj.basicOpen (quotientGrading mu nu)
      (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (0 : Fin 5)))).toScheme ≅
    Spec (.of (affineRing mu nu)) :=
  Proj.basicOpenIsoSpec (quotientGrading mu nu) _
      ((quotientMap mu nu).map_mem (Slot02HighProjSpace.X_mem_one K 4 0)) one_pos ≪≫
    Scheme.Spec.mapIso ((chartEquiv mu nu).symm.toCommRingCatIso.op)

end FourCorner.OppositeProjective.PostPChart
#print axioms FourCorner.OppositeProjective.PostPChart.chartSchemeIso
