import FiveRootUniversal
import ResidueGenerators
import GenericFieldPoint

noncomputable section
namespace FourCorner.FiveRadicalEmbedding
open IntermediateField Genus17Geometry
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

/-- The actual five-root field is the universal monic degree32 algebra.
This identifies each separately ordered radical, rather than assuming a
function-field comparison or an embedding into the target field. -/
def literalEquiv (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) :
    FiveRootUniversal.A (RatFunc ℚ) (CommonFiveIndependence.value t κ) ≃ₐ[RatFunc ℚ]
      CommonGenus17Field.field ℚ t κ :=
  FiveRootUniversal.equiv _ (fiveRoot t κ) (ResidueGenerators.fiveRoot_sq ℚ t κ)
    (ResidueGenerators.fiveRoot_generates ℚ t κ)
    (ResidueRadicalDegree.degree_thirty_two ℚ (by linarith) (by linarith) (by linarith) hκ)

@[simp] theorem literalEquiv_coord (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) (i : Fin 5) :
    literalEquiv t κ ht hκ (FiveRootUniversal.coord (RatFunc ℚ) (CommonFiveIndependence.value t κ) i) =
      fiveRoot t κ i :=
  FiveRootUniversal.lift_coord _ (algebraMap _ _) _ _ (ResidueGenerators.fiveRoot_sq ℚ t κ) i

variable {L : Type} [Field L] [CharZero L]
def baseEmbedding (e : L) (he : Transcendental ℚ e) : RatFunc ℚ →+* L :=
  (IntermediateField.val ℚ⟮e⟯).toRingHom.comp (RatFunc.algEquivOfTranscendental e he).toRingHom
@[simp] theorem baseEmbedding_X (e : L) (he : Transcendental ℚ e) :
    baseEmbedding e he RatFunc.X = e := RatFunc.algEquivOfTranscendental_X e he
@[simp] theorem baseEmbedding_coeff (e : L) (he : Transcendental ℚ e) (q : ℚ) :
    baseEmbedding e he (algebraMap ℚ (RatFunc ℚ) q) = algebraMap ℚ L q := by
  simp only [eq_ratCast,map_ratCast,Rat.cast_id]

def embedding (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) (e : L) (he : Transcendental ℚ e)
    (r : Fin 5 → L) (hr : ∀ i, r i^2 = baseEmbedding e he (CommonFiveIndependence.value t κ i)) :
    CommonGenus17Field.field ℚ t κ →+* L :=
  (FiveRootUniversal.lift _ (baseEmbedding e he) _ r hr).comp
    (literalEquiv t κ ht hκ).symm.toRingHom

@[simp] theorem embedding_root (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) (e : L)
    (he : Transcendental ℚ e) (r : Fin 5 → L)
    (hr : ∀ i, r i^2 = baseEmbedding e he (CommonFiveIndependence.value t κ i)) (i : Fin 5) :
    embedding t κ ht hκ e he r hr (fiveRoot t κ i) = r i := by
  rw [← literalEquiv_coord t κ ht hκ i]
  change (FiveRootUniversal.lift _ (baseEmbedding e he) _ r hr)
    ((literalEquiv t κ ht hκ).symm ((literalEquiv t κ ht hκ) _)) = _
  rw [AlgEquiv.symm_apply_apply,FiveRootUniversal.lift_coord]

@[simp] theorem embedding_base (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) (e : L)
    (he : Transcendental ℚ e) (r : Fin 5 → L)
    (hr : ∀ i, r i^2 = baseEmbedding e he (CommonFiveIndependence.value t κ i)) (x : RatFunc ℚ) :
    embedding t κ ht hκ e he r hr (algebraMap (RatFunc ℚ) (CommonGenus17Field.field ℚ t κ) x) =
      baseEmbedding e he x := by
  change (FiveRootUniversal.lift _ (baseEmbedding e he) _ r hr)
    ((literalEquiv t κ ht hκ).symm (algebraMap _ _ x)) = _
  rw [AlgEquiv.commutes,FiveRootUniversal.lift_algebraMap]

@[simp] theorem embedding_ell (t κ : ℚ) (ht : 1<t) (hκ : κ ≠ 0) (e : L)
    (he : Transcendental ℚ e) (r : Fin 5 → L)
    (hr : ∀ i, r i^2 = baseEmbedding e he (CommonFiveIndependence.value t κ i)) :
    embedding t κ ht hκ e he r hr (Genus17Geometry.ell t κ) = e := by
  change embedding t κ ht hκ e he r hr (algebraMap (RatFunc ℚ) _ RatFunc.X) = _
  rw [embedding_base,baseEmbedding_X]

end FourCorner.FiveRadicalEmbedding
#print axioms FourCorner.FiveRadicalEmbedding.literalEquiv
#print axioms FourCorner.FiveRadicalEmbedding.embedding
#print axioms FourCorner.FiveRadicalEmbedding.embedding_root
#print axioms FourCorner.FiveRadicalEmbedding.embedding_ell
