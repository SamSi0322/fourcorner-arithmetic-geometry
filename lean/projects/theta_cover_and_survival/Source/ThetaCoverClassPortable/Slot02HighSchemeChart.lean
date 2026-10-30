import ThetaCoverClassPortable.Slot02HighChart

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
namespace FourCorner.OppositeProjective.HighChart
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The actual basic-open subscheme of the literal three-quadric Proj is the affine scheme of its equations. -/
def chartSchemeIso (mu nu : K) :
    (Proj.basicOpen (quotientGrading mu nu)
      (Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (MvPolynomial.X (4 : Fin 5)))).toScheme ≅
    Spec (.of (affineRing mu nu)) :=
  Proj.basicOpenIsoSpec (quotientGrading mu nu) _
      ((quotientMap mu nu).map_mem (Slot02HighProjSpace.X_mem_one K 4 4)) one_pos ≪≫
    Scheme.Spec.mapIso ((chartEquiv mu nu).symm.toCommRingCatIso.op)

end FourCorner.OppositeProjective.HighChart
#print axioms FourCorner.OppositeProjective.HighChart.chartSchemeIso
