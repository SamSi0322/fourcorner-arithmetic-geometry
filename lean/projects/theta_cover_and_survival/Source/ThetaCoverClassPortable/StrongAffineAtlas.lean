import ThetaCoverClassPortable.OpenImmersionPoints

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal

variable (K : Type) [Field K] [Algebra ℚ K] [TopologicalSpace K]

/-- Every genuine K-point belongs to an actual affine open chart over QQ. -/
theorem exists_affine_chart_through_point (X : Over base) (P : KPoints K X) :
    ∃ (A : CommAlgCat ℚ) (j : pointObject A ⟶ X) (p : A →ₐ[ℚ] K),
      IsOpenImmersion j.left ∧ affineTest K A j p=P := by
  obtain ⟨A,f,hf,hx,_⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X:=X.left) (U:=⊤) (show pointSupport K P ∈ (⊤ : X.left.Opens) from trivial)
  let qmap : ℚ →+* A := (Spec.preimage (f ≫ X.hom)).hom
  letI : Algebra ℚ A := qmap.toAlgebra
  letI : IsOpenImmersion f := hf
  have hb : f ≫ X.hom=(pointObject A).hom := (Spec.map_preimage (f ≫ X.hom)).symm
  let j : pointObject A ⟶ X := Over.homMk f hb
  letI : IsOpenImmersion j.left := hf
  let Q := openPointLift K j P hx
  refine ⟨CommAlgCat.of ℚ A,j,pointToAlgHom A K Q,hf,?_⟩
  change pointChange (pointToAlgHom A K Q) ≫ j=P
  rw [pointChange_pointToAlgHom]
  exact openPointLift_comp K j P hx

variable [IsTopologicalDivisionRing K] [T1Space K]

/-- Actual affine evaluation charts form an open atlas for the canonical strong topology. -/
theorem actual_strong_affine_atlas (X : Over base) (P : KPoints K X) :
    ∃ (A : CommAlgCat ℚ) (j : pointObject A ⟶ X) (p : A →ₐ[ℚ] K),
      IsOpenImmersion j.left ∧ affineTest K A j p=P ∧
        Topology.IsOpenEmbedding (affineTest K A j) := by
  obtain ⟨A,j,p,hj,hp⟩ := exists_affine_chart_through_point K X P
  letI := hj
  refine ⟨A,j,p,hj,hp,?_⟩
  have h := (isOpenEmbedding_pointMap K j).comp
    (affineSchemePointsHomeomorph K A).symm.isOpenEmbedding
  exact h

end FourCorner.ThetaLocalSurvival.StrongTopology
