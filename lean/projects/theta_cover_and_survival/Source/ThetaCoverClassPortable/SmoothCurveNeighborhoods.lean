import ThetaCoverClassPortable.SmoothAffineEtaleCoordinate
import Mathlib.Topology.Algebra.Module.PerfectSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal

variable (K : Type) [NontriviallyNormedField K] [Algebra ℚ K] [CompleteSpace K]

/-- Every actual strong-topology neighborhood of a smooth affine curve point is infinite. -/
theorem smooth_affine_neighborhood_infinite (A : Type) [CommRing A] [Algebra ℚ A]
    [SmoothOfRelativeDimension 1 (pointObject A).hom]
    (φ : A →ₐ[ℚ] K) (U : Set (A →ₐ[ℚ] K)) (hU : U∈𝓝 φ) : U.Infinite := by
  obtain ⟨r,hr,t,ht⟩ := smooth_affine_exists_etale_coordinate A K φ
  let S := Localization.Away r
  let q : S →ₐ[ℚ] K := localizationPointLift ℚ A K r S ⟨φ,hr⟩
  let red : (S →ₐ[ℚ] K) → (A →ₐ[ℚ] K) := fun f => f.comp (Algebra.algHom ℚ A S)
  have hred : red q=φ := by
    ext a
    exact localizationPointLift_algebraMap ℚ A K r S ⟨φ,hr⟩ a
  have hV : red ⁻¹' U ∈ 𝓝 q := by
    have h := (continuous_precomposition (K:=K) (Algebra.algHom ℚ A S)).tendsto q
    change Filter.Tendsto red (𝓝 q) (𝓝 (red q)) at h
    rw [hred] at h
    exact h hU
  letI : Algebra (MvPolynomial (Fin 1) ℚ) S := t.toRingHom.toAlgebra
  letI : IsScalarTower ℚ (MvPolynomial (Fin 1) ℚ) S :=
    IsScalarTower.of_algebraMap_eq' t.comp_algebraMap.symm
  letI : Algebra.Etale (MvPolynomial (Fin 1) ℚ) S := ht
  have hc := (affineLinePointsHomeomorph ℚ K).isLocalHomeomorph.comp
    (etale_affine_points_localHomeomorph (MvPolynomial (Fin 1) ℚ) S K)
  let c : (S →ₐ[ℚ] K) → K := (affineLinePointsHomeomorph ℚ K) ∘
    (fun f => f.comp (Algebra.algHom ℚ (MvPolynomial (Fin 1) ℚ) S))
  have hcV : c '' (red ⁻¹' U) ∈ 𝓝 (c q) := by
    rw [←hc.map_nhds_eq q]
    exact Filter.image_mem_map hV
  have hi : (red ⁻¹' U).Infinite := (infinite_of_mem_nhds (c q) hcV).of_image
  have hredinj : Function.Injective red := by
    intro f g h
    exact IsLocalization.algHom_ext (Submonoid.powers r) h
  exact (hi.image hredinj.injOn).mono (Set.image_preimage_subset red U)

/-- Every genuine local-field point of an actual smooth QQ curve has infinitely many
actual local-field points in every canonical strong-topology neighborhood. -/
theorem smooth_curve_neighborhood_infinite (X : Over base) [SmoothOfRelativeDimension 1 X.hom]
    (P : KPoints K X) (U : Set (KPoints K X)) (hU : U∈𝓝 P) : U.Infinite := by
  obtain ⟨A,j,p,hj,hp⟩ := exists_affine_chart_through_point K X P
  letI := hj
  letI : SmoothOfRelativeDimension 1 (pointObject A).hom := by
    rw [←j.w]
    have h : SmoothOfRelativeDimension (0+1) (j.left≫X.hom) := inferInstance
    exact h
  have hpre : (affineTest K A j) ⁻¹' U∈𝓝 p := by
    have h := (continuous_affineTest K A j).tendsto p
    rw [hp] at h
    exact h hU
  have hi := smooth_affine_neighborhood_infinite K A p _ hpre
  have he := (isOpenEmbedding_pointMap K j).comp
    (affineSchemePointsHomeomorph K A).symm.isOpenEmbedding
  exact (hi.image he.injective.injOn).mono (Set.image_preimage_subset _ _)

end FourCorner.ThetaLocalSurvival.StrongTopology
