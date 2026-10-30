import HpSchemeModel
import HpResidueCharts
import FourRootLift08
import FiveRadicalEmbedding

namespace FourCorner.HpModelFieldPoint
open AlgebraicCurve AlgebraicGeometry CategoryTheory HpLiteralField HpFieldGeometry HpResidueCharts
open FiveRadicalEmbedding
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- The actual literal degree-sixteen field is the universal algebra of
these same four linear radicands, preserving each separately ordered root. -/
def literalEquiv (p : ℚ) (hp : 1<p) :
    FourRootLift08.A (RatFunc ℚ) (radicand ℚ p) ≃ₐ[RatFunc ℚ] field ℚ p :=
  FourRootLift08.equiv _ (root ℚ p) (root_sq ℚ p)
    (root_generates ℚ p) (field_degree_sixteen ℚ p (by linarith) (by linarith) (by linarith))

variable {L : Type} [Field L] [CharZero L]

theorem radicand_evaluation (p : ℚ) (e : L) (he : Transcendental ℚ e) (i : Fin 4) :
    baseEmbedding e he (radicand ℚ p i)=values (p : L) e i := by
  fin_cases i <;> simp only [radicand,poly,values,map_mul,map_add,map_sub,map_one,map_ofNat,
    RatFunc.algebraMap_C,RatFunc.algebraMap_X,← RatFunc.algebraMap_eq_C,
    baseEmbedding_coeff,baseEmbedding_X] <;> simp only [eq_ratCast,map_ratCast,Rat.cast_id] <;> ring

/-- A Q-transcendental source solution embeds the SAME literal function
field into the completion or real field. -/
def fieldEmbedding (p : ℚ) (hp : 1<p) (e : L) (he : Transcendental ℚ e) (r : Fin 4 → L)
    (hr : ∀i,r i^2=values (p : L) e i) : field ℚ p →+* L :=
  (FourRootLift08.lift (RatFunc ℚ) (baseEmbedding e he) (radicand ℚ p) r
    (fun i => (hr i).trans (radicand_evaluation p e he i).symm)).comp
    (literalEquiv p hp).symm.toRingHom

/-- Actual Spec(L) point of the same smooth proper model, constructed from
its generic stalk through an actual injective function-field map. -/
def point (p : ℚ) (hp : 1<p) (e : L) (he : Transcendental ℚ e) (r : Fin 4 → L)
    (hr : ∀i,r i^2=values (p : L) e i) :
    Spec (CommRingCat.of L) ⟶ HpSchemeModel.curve p := by
  letI := HpSchemeModel.modelFieldAlgebra p
  exact GenericFieldPoint.pointOfEmbedding (HpSchemeModel.model p) (fieldEmbedding p hp e he r hr)

theorem point_overQ (p : ℚ) (hp : 1<p) (e : L) (he : Transcendental ℚ e) (r : Fin 4 → L)
    (hr : ∀i,r i^2=values (p : L) e i) :
    point p hp e he r hr ≫ HpSchemeModel.toBase p=Spec.map (CommRingCat.ofHom (algebraMap ℚ L)) := by
  letI := HpSchemeModel.modelFieldAlgebra p
  exact GenericFieldPoint.pointOfEmbedding_over _ _

#print axioms literalEquiv
#print axioms fieldEmbedding
#print axioms point
#print axioms point_overQ
end
end FourCorner.HpModelFieldPoint
