import FourRootLift08
import RealTranscendentalSource08
noncomputable section
namespace FourCorner.RealFieldEmbedding08
open CommonLiteralField IntermediateField

/-- The universal four-quadratic algebra is the actual degree16 field. -/
def literalEquiv (t : ℚ) (ht : 1<t) :
    FourRootLift08.A (RatFunc ℚ) (radicand ℚ t) ≃ₐ[RatFunc ℚ] field ℚ t := by
  have hd := finrank_field_eq_sixteen ℚ (t:=t) (by linarith) (by linarith) (by linarith)
  letI : FiniteDimensional (RatFunc ℚ) (field ℚ t) := Module.finite_of_finrank_pos (by rw [hd]; norm_num)
  apply FourRootLift08.equiv (radicand ℚ t) (root ℚ t) (root_sq ℚ t) ?_ hd
  exact (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic (by
    rintro _ ⟨i,rfl⟩
    exact (IsIntegral.of_finite (RatFunc ℚ) (root ℚ t i)).isAlgebraic)).mp (root_adjoin_eq_top ℚ t)

@[simp] theorem literalEquiv_coord (t : ℚ) (ht : 1<t) (k : Fin 4) :
    literalEquiv t ht (FourRootLift08.coord (RatFunc ℚ) (radicand ℚ t) k) = root ℚ t k :=
  FourRootLift08.lift_coord (RatFunc ℚ) (algebraMap (RatFunc ℚ) (field ℚ t))
    (radicand ℚ t) (root ℚ t) (root_sq ℚ t) k

def baseEmbedding (e : ℝ) (he : Transcendental ℚ e) : RatFunc ℚ →+* ℝ :=
  (IntermediateField.val ℚ⟮e⟯).toRingHom.comp (RatFunc.algEquivOfTranscendental e he).toRingHom

@[simp] theorem baseEmbedding_X (e : ℝ) (he : Transcendental ℚ e) :
    baseEmbedding e he RatFunc.X = e := by
  exact RatFunc.algEquivOfTranscendental_X e he

@[simp] theorem baseEmbedding_coeff (e : ℝ) (he : Transcendental ℚ e) (q : ℚ) :
    baseEmbedding e he (algebraMap ℚ (RatFunc ℚ) q) = q := by
  simp only [eq_ratCast,map_ratCast,Rat.cast_id]

def sourceRoots {t : ℚ} (S : CommonRootSource ℝ (t:ℝ)) : Fin 4 → ℝ := ![S.P,S.C,S.M,S.B]

theorem sourceRoots_sq {t : ℚ} (S : CommonRootSource ℝ (t:ℝ))
    (he : Transcendental ℚ S.ell) (k : Fin 4) :
    sourceRoots S k ^ 2 = baseEmbedding S.ell he (radicand ℚ t k) := by
  fin_cases k
  · simpa [sourceRoots,radicand] using S.sqP
  · simpa [sourceRoots,radicand] using S.sqC
  · simpa [sourceRoots,radicand] using S.sqM
  · simpa [sourceRoots,radicand] using S.sqB

/-- A literal transcendental strict real source produces an actual field
embedding, with every original coordinate fixed individually. -/
def embedding (t : ℚ) (ht : 1<t) (S : CommonRootSource ℝ (t:ℝ))
    (he : Transcendental ℚ S.ell) : field ℚ t →+* ℝ :=
  (FourRootLift08.lift _ (baseEmbedding S.ell he) (radicand ℚ t) (sourceRoots S)
    (sourceRoots_sq S he)).comp (literalEquiv t ht).symm.toRingHom

@[simp] theorem embedding_root (t : ℚ) (ht : 1<t) (S : CommonRootSource ℝ (t:ℝ))
    (he : Transcendental ℚ S.ell) (k : Fin 4) :
    embedding t ht S he (root ℚ t k) = sourceRoots S k := by
  rw [← literalEquiv_coord t ht k]
  change (FourRootLift08.lift _ (baseEmbedding S.ell he) (radicand ℚ t) (sourceRoots S)
    (sourceRoots_sq S he)) ((literalEquiv t ht).symm
      ((literalEquiv t ht) (FourRootLift08.coord _ (radicand ℚ t) k))) = _
  rw [AlgEquiv.symm_apply_apply,FourRootLift08.lift_coord]

@[simp] theorem embedding_base (t : ℚ) (ht : 1<t) (S : CommonRootSource ℝ (t:ℝ))
    (he : Transcendental ℚ S.ell) (x : RatFunc ℚ) :
    embedding t ht S he (algebraMap (RatFunc ℚ) (field ℚ t) x) = baseEmbedding S.ell he x := by
  change (FourRootLift08.lift _ (baseEmbedding S.ell he) (radicand ℚ t) (sourceRoots S)
    (sourceRoots_sq S he)) ((literalEquiv t ht).symm (algebraMap (RatFunc ℚ) (field ℚ t) x)) = _
  rw [AlgEquiv.commutes,FourRootLift08.lift_algebraMap]

@[simp] theorem embedding_ell (t : ℚ) (ht : 1<t) (S : CommonRootSource ℝ (t:ℝ))
    (he : Transcendental ℚ S.ell) : embedding t ht S he (ell ℚ t) = S.ell := by
  simp only [ell,embedding_base,baseEmbedding_X]

#print axioms literalEquiv
#print axioms embedding
#print axioms embedding_root
#print axioms embedding_ell
end FourCorner.RealFieldEmbedding08
