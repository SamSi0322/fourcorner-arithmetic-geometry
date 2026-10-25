import Genus17GeometricField
import geometry.SchemeModelGeometricIntegral
import Mathlib.AlgebraicGeometry.Geometrically.Connected

noncomputable section
namespace FourCorner.Genus17Geometry
open AlgebraicGeometry AlgebraicCurve CategoryTheory
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

abbrev modelCover (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    (curve t κ h0 h1 hm).TwoAffineOpenCover := by
  letI := finite_over_line t κ h0 h1 hm
  exact SchemeModelFiniteExtension.twoAffineOpenCover K (field t κ)

lemma cover0Nonempty (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Nonempty (modelCover t κ h0 h1 hm).U0 := by
  letI := finite_over_line t κ h0 h1 hm
  exact SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U0 K (field t κ)
lemma cover1Nonempty (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Nonempty (modelCover t κ h0 h1 hm).U1 := by
  letI := finite_over_line t κ h0 h1 hm
  exact SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U1 K (field t κ)
lemma cover01Nonempty (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Nonempty ((modelCover t κ h0 h1 hm).U0 ⊓ (modelCover t κ h0 h1 hm).U1 : (curve t κ h0 h1 hm).Opens) := by
  letI := finite_over_line t κ h0 h1 hm
  exact SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_overlap K (field t κ)

/-- Geometric integrality of the actual same canonical five-root model under
arbitrary field-valued Scheme base change, from genuine tensor domains. -/
theorem model_geometricallyIntegral (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    GeometricallyIntegral (toBase t κ h0 h1 hm) := by
  letI := finite_over_line t κ h0 h1 hm
  exact SchemeModelGeometricIntegral.model_geometricallyIntegral K (field t κ)
    (fun L _ _ => Genus17GeometricField.all_constants_domain K L h0 h1 hm hκ)

theorem model_geometricallyConnected (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    GeometricallyConnected (toBase t κ h0 h1 hm) := by
  have h := model_geometricallyIntegral t κ h0 h1 hm hκ
  refine ⟨fun {L} _ y {Z} fst snd hpb => ?_⟩
  have := h.geometrically_isIntegral y fst snd hpb
  infer_instance
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.model_geometricallyIntegral
#print axioms FourCorner.Genus17Geometry.model_geometricallyConnected
