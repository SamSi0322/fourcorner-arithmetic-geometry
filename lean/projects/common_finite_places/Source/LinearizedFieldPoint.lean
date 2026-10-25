import FiveRadicalEmbedding
import RadicalLinearization

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.LinearizedFieldPoint
open FiveRadicalEmbedding
variable {L : Type} [Field L] [CharZero L]

def recover (r : Fin 5 → L) : Fin 5 → L
  | 0 => r 0
  | 1 => r 1
  | 2 => r 2 / r 4
  | 3 => r 3 / r 4
  | 4 => r 4

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

theorem recovered_squares (t κ : ℚ) (hκ : κ ≠ 0) (e : L) (he : Transcendental ℚ e)
    (r : Fin 5 → L)
    (hr : ∀ i, r i ^ 2 = RadicalLinearization.values (t : L) ((κ : L)⁻¹) e i)
    (i : Fin 5) :
    recover r i ^ 2 = baseEmbedding e he (CommonFiveIndependence.value t κ i) := by
  have hk : (κ : L) ≠ 0 := by exact_mod_cast hκ
  have he0 : e ≠ 0 := by intro hz; apply he; rw [hz]; exact isAlgebraic_zero
  have h4 := hr 4
  change r 4 ^ 2 = e*(κ : L)⁻¹ at h4
  have hr4 : r 4 ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide)] at h4
    exact (mul_ne_zero he0 (inv_ne_zero hk)) h4.symm
  fin_cases i <;> dsimp only [recover]
  all_goals try rw [div_pow]
  all_goals rw [hr]
  all_goals try rw [h4]
  all_goals simp only [RadicalLinearization.values,CommonFiveIndependence.value,
    CommonLiteralField.radicand,map_add,map_sub,map_mul,map_div₀,map_inv₀,
    baseEmbedding_X,baseEmbedding_coeff,map_one]
  all_goals simp only [eq_ratCast,map_ratCast]
  all_goals first | rfl | (field_simp [hk,he0] <;> ring)

/-- A transcendental solution of the linearized five equations constructs
an actual embedding of the SAME literal Q-function field into L. -/
def fieldEmbedding (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) (e : L)
    (he : Transcendental ℚ e) (r : Fin 5 → L)
    (hr : ∀ i, r i ^ 2 = RadicalLinearization.values (t : L) ((κ : L)⁻¹) e i) :
    CommonGenus17Field.field ℚ t κ →+* L :=
  embedding t κ ht hκ e he (recover r) (recovered_squares t κ hκ e he r hr)

/-- The realized point belongs to the original canonical genus17 cover,
with actual generic-stalk factorization, rather than a labelled equation tuple. -/
def point (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) (e : L)
    (he : Transcendental ℚ e) (r : Fin 5 → L)
    (hr : ∀ i, r i ^ 2 = RadicalLinearization.values (t : L) ((κ : L)⁻¹) e i) :
    Spec (CommRingCat.of L) ⟶ Genus17Geometry.curve t κ (by linarith) (by linarith) (by linarith) :=
  by
    letI := Genus17Geometry.modelFieldAlgebra t κ
    exact GenericFieldPoint.pointOfEmbedding (Genus17Geometry.model t κ (by linarith) (by linarith) (by linarith))
      (fieldEmbedding t κ ht hκ e he r hr)

theorem point_overQ (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) (e : L)
    (he : Transcendental ℚ e) (r : Fin 5 → L)
    (hr : ∀ i, r i ^ 2 = RadicalLinearization.values (t : L) ((κ : L)⁻¹) e i) :
    point t κ ht hκ e he r hr ≫ Genus17Geometry.toBase t κ (by linarith) (by linarith) (by linarith) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ L)) :=
  by
    letI := Genus17Geometry.modelFieldAlgebra t κ
    exact GenericFieldPoint.pointOfEmbedding_over _ _

theorem fieldEmbedding_coordinate (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) (e : L)
    (he : Transcendental ℚ e) (r : Fin 5 → L)
    (hr : ∀ i, r i ^ 2 = RadicalLinearization.values (t : L) ((κ : L)⁻¹) e i) (i : Fin 5) :
    fieldEmbedding t κ ht hκ e he r hr (Genus17Geometry.fiveRoot t κ i) = recover r i :=
  embedding_root _ _ _ _ _ _ _ _ i

theorem fieldEmbedding_ell (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) (e : L)
    (he : Transcendental ℚ e) (r : Fin 5 → L)
    (hr : ∀ i, r i ^ 2 = RadicalLinearization.values (t : L) ((κ : L)⁻¹) e i) :
    fieldEmbedding t κ ht hκ e he r hr (Genus17Geometry.ell t κ) = e :=
  embedding_ell _ _ _ _ _ _ _ _

end FourCorner.LinearizedFieldPoint
#print axioms FourCorner.LinearizedFieldPoint.recovered_squares
#print axioms FourCorner.LinearizedFieldPoint.point
#print axioms FourCorner.LinearizedFieldPoint.point_overQ
#print axioms FourCorner.LinearizedFieldPoint.fieldEmbedding_coordinate
