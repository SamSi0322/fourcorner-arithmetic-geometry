import ThetaLocalSurvivalPortable.AffinePointAlgebra
import Mathlib.Topology.Algebra.Field
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open AlgebraicGeometry CategoryTheory
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology

universe u v w
variable (R : Type u) [CommRing R]
variable (A : Type v) [CommRing A] [Algebra R A]
variable (K : Type w) [CommRing K] [Algebra R K] [TopologicalSpace K]

/-- The usual topology of pointwise evaluation on affine field-valued points. -/
instance affinePointTopology : TopologicalSpace (A →ₐ[R] K) :=
  TopologicalSpace.induced (fun f : A →ₐ[R] K => (f : A → K)) inferInstance

theorem affinePoint_isEmbedding :
    Topology.IsEmbedding (fun f : A →ₐ[R] K => (f : A → K)) :=
  (show Function.Injective (fun f : A →ₐ[R] K => (f : A → K)) from
    fun _ _ h => DFunLike.coe_injective h).isEmbedding_induced

theorem continuous_evaluation (a : A) : Continuous (fun f : A →ₐ[R] K => f a) :=
  (continuous_apply a).comp (affinePoint_isEmbedding R A K).continuous

theorem continuous_affine_iff {T : Type*} [TopologicalSpace T]
    (f : T → (A →ₐ[R] K)) : Continuous f ↔ ∀ a, Continuous (fun t => f t a) := by
  rw [(affinePoint_isEmbedding R A K).isInducing.continuous_iff, continuous_pi_iff]
  rfl

instance affinePointT2 [T2Space K] : T2Space (A →ₐ[R] K) :=
  (affinePoint_isEmbedding R A K).t2Space

variable {R A K} {B : Type*} [CommRing B] [Algebra R B]

theorem continuous_precomposition (f : A →ₐ[R] B) :
    Continuous (fun g : B →ₐ[R] K => g.comp f) := by
  apply (continuous_affine_iff R A K _).2
  intro a
  exact continuous_evaluation R B K (f a)

/-- A change of affine coordinate ring induces the canonical homeomorphism on points. -/
def affinePointsHomeomorph (e : A ≃ₐ[R] B) : (B →ₐ[R] K) ≃ₜ (A →ₐ[R] K) where
  toEquiv :=
    { toFun := fun f => f.comp e.toAlgHom
      invFun := fun f => f.comp e.symm.toAlgHom
      left_inv := by intro f; ext a; simp
      right_inv := by intro f; ext a; simp }
  continuous_toFun := continuous_precomposition e.toAlgHom
  continuous_invFun := continuous_precomposition e.symm.toAlgHom

end FourCorner.ThetaLocalSurvival.StrongTopology
