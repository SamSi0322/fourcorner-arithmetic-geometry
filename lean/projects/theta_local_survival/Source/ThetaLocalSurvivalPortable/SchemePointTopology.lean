import ThetaLocalSurvivalPortable.LocalizationPointHomeomorph
import Mathlib.Algebra.Category.CommAlgCat.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal

variable (K : Type) [Field K] [Algebra ℚ K] [TopologicalSpace K]

/-- Actual over-QQ morphisms from Spec K. -/
abbrev KPoints (X : Over base) := pointObject K ⟶ X

/-- An affine test chart on actual scheme-valued points. -/
def affineTest {X : Over base} (A : CommAlgCat ℚ) (j : pointObject A ⟶ X)
    (f : A →ₐ[ℚ] K) : KPoints K X := pointChange f ≫ j

/-- The canonical strong topology: the final topology for affine evaluation charts.
All affine test morphisms are allowed, making functoriality intrinsic. The theorem
`affineSchemePointsHomeomorph` proves exact agreement with affine evaluation topology. -/
instance schemePointTopology (X : Over base) : TopologicalSpace (KPoints K X) :=
  ⨆ (A : CommAlgCat ℚ) (j : pointObject A ⟶ X),
    TopologicalSpace.coinduced (affineTest K A j) inferInstance

theorem continuous_affineTest {X : Over base} (A : CommAlgCat ℚ)
    (j : pointObject A ⟶ X) : Continuous (affineTest K A j) :=
  continuous_iSup_rng (i:=A) (continuous_iSup_rng (i:=j) continuous_coinduced_rng)

theorem continuous_schemePoints_iff {X : Over base} {T : Type*} [TopologicalSpace T]
    (f : KPoints K X → T) :
    Continuous f ↔ ∀ (A : CommAlgCat ℚ) (j : pointObject A ⟶ X),
      Continuous (fun p : A →ₐ[ℚ] K => f (affineTest K A j p)) := by
  change Continuous[⨆ (A : CommAlgCat ℚ) (j : pointObject A ⟶ X),
    TopologicalSpace.coinduced (affineTest K A j) inferInstance, inferInstance] f ↔ _
  simp only [continuous_iSup_dom, continuous_coinduced_dom]
  rfl

theorem continuous_pointMap {X Y : Over base} (f : X ⟶ Y) :
    Continuous (fun P : KPoints K X => P ≫ f) := by
  apply (continuous_schemePoints_iff K _).2
  intro A j
  change Continuous (fun p : A →ₐ[ℚ] K => (pointChange p ≫ j) ≫ f)
  have h : (fun p : A →ₐ[ℚ] K => (pointChange p ≫ j) ≫ f) = affineTest K A (j ≫ f) :=
    funext (fun p => Category.assoc _ _ _)
  rw [h]
  exact continuous_affineTest K A (j ≫ f)

theorem continuous_pointToAlgHom (A : Type) [CommRing A] [Algebra ℚ A] :
    Continuous (pointToAlgHom A K) := by
  apply (continuous_schemePoints_iff K _).2
  intro B j
  have h : (fun p : B →ₐ[ℚ] K => pointToAlgHom A K (affineTest K B j p)) =
      (fun p => p.comp (pointToAlgHom A B j)) := by
    funext p
    exact pointToAlgHom_natural p j
  rw [h]
  exact continuous_precomposition _

/-- On an affine scheme, the canonical scheme point topology is exactly evaluation topology. -/
def affineSchemePointsHomeomorph (A : Type) [CommRing A] [Algebra ℚ A] :
    KPoints K (pointObject A) ≃ₜ (A →ₐ[ℚ] K) where
  toEquiv := affinePointsEquiv A K
  continuous_toFun := continuous_pointToAlgHom K A
  continuous_invFun := by
    change Continuous (fun p : A →ₐ[ℚ] K => pointChange p)
    have h := continuous_affineTest K (CommAlgCat.of ℚ A) (𝟙 (pointObject A))
    change Continuous (fun p : A →ₐ[ℚ] K => pointChange p ≫ 𝟙 _) at h
    simpa only [Category.comp_id] using h

/-- Scheme isomorphisms give homeomorphisms of their genuine K-points. -/
def schemeIsoPointsHomeomorph {X Y : Over base} (e : X ≅ Y) : KPoints K X ≃ₜ KPoints K Y where
  toEquiv :=
    { toFun := fun P => P ≫ e.hom
      invFun := fun P => P ≫ e.inv
      left_inv := by intro P; simp
      right_inv := by intro P; simp }
  continuous_toFun := continuous_pointMap K e.hom
  continuous_invFun := continuous_pointMap K e.inv

end FourCorner.ThetaLocalSurvival.StrongTopology
