import ThetaCoverClassPortable.ThetaSourcePresentation
import ThetaCoverClassPortable.ThetaPairPresentation
noncomputable section
namespace FourCorner.ThetaSourcePairData
open Algebra AlgebraicGeometry
open ThetaQuotientCharts ThetaChartAlgebras
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def inducedQ {R V : Type} [CommRing R] [CommRing V] [Algebra ℚ R] [Algebra R V] : Algebra ℚ V :=
  ((algebraMap R V).comp (algebraMap ℚ R)).toAlgebra
private theorem inducedTower {R V : Type} [CommRing R] [CommRing V] [Algebra ℚ R] [Algebra R V] :
    letI := inducedQ (R:=R) (V:=V); IsScalarTower ℚ R V := by
  letI := inducedQ (R:=R) (V:=V)
  exact IsScalarTower.of_algebraMap_eq (R:=ℚ) (S:=R) (A:=V) (fun _=>rfl)

def lift (j : Fin 3) {V : Type} [CommRing V] [Algebra (R j) V] (x y : V)
    (hx : x^2=algebraMap (R j) V (a j)) (hy : y^2=algebraMap (R j) V (b j))
    (hc : x*y=algebraMap (R j) V (c j)) : S j →ₐ[R j] V := by
  letI := inducedQ (R:=R j) (V:=V)
  letI := inducedTower (R:=R j) (V:=V)
  exact ThetaSourcePresentation.ofUTR j x y hx hy hc
lemma lift_u (j : Fin 3) {V : Type} [CommRing V] [Algebra (R j) V] (x y : V) (hx) (hy) (hc) :
    lift j x y hx hy hc (u j)=x := by
  letI := inducedQ (R:=R j) (V:=V)
  letI := inducedTower (R:=R j) (V:=V)
  change ThetaSourcePresentation.ofUTR j x y hx hy hc (u j)=x
  exact ThetaSourcePresentation.ofUTR_u j x y hx hy hc
lemma lift_v (j : Fin 3) {V : Type} [CommRing V] [Algebra (R j) V] (x y : V) (hx) (hy) (hc) :
    lift j x y hx hy hc (t j)=y := by
  letI := inducedQ (R:=R j) (V:=V)
  letI := inducedTower (R:=R j) (V:=V)
  change ThetaSourcePresentation.ofUTR j x y hx hy hc (t j)=y
  exact ThetaSourcePresentation.ofUTR_t j x y hx hy hc
lemma hom_ext (j : Fin 3) {V : Type} [CommRing V] [Algebra (R j) V] {f g : S j →ₐ[R j] V}
    (hu : f (u j)=g (u j)) (ht : f (t j)=g (t j)) : f=g := by
  letI := inducedQ (R:=R j) (V:=V)
  letI := inducedTower (R:=R j) (V:=V)
  exact ThetaSourcePresentation.hom_ext j hu ht

/-- Exact pair presentation of each original P/Q/R chart over its literal quartic chart. -/
def data (j : Fin 3) : ThetaPairPresentation.Data (R j) (S j) where
  a:=a j
  b:=b j
  c:=c j
  u:=u j
  v:=t j
  base_conic:=base_conic j
  u_sq:=source_u_sq j
  v_sq:=source_t_sq j
  uv:=source_ut j
  lift:=lift j
  lift_u:=lift_u j
  lift_v:=lift_v j
  hom_ext:=hom_ext j
end FourCorner.ThetaSourcePairData
#print axioms FourCorner.ThetaSourcePairData.data
