import ThetaCoverClassPortable.SmoothCurveNeighborhoods
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal

/-- In a Jacobson space every point of a finite closed subset is a closed point. -/
theorem finite_closed_subset_closedPoints {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    (B : Set T) (hB : B.Finite) (hBc : IsClosed B) : B⊆closedPoints T := by
  have hc : IsClosed (B∩closedPoints T) := by
    rw [←(B∩closedPoints T).biUnion_of_singleton]
    exact (hB.subset Set.inter_subset_left).isClosed_biUnion (fun x hx => hx.2)
  have he : B∩closedPoints T=B := hc.closure_eq.symm.trans (closure_inter_closedPoints hBc)
  intro x hx
  exact (he.symm ▸ hx).2

variable (X : Over base) [LocallyOfFiniteType X.hom] (K : Type) [Field K] [Algebra ℚ K]

/-- Actual residue-field embeddings at a closed point form a finite type.
Finiteness is derived from the QQ structural map, not supplied as a boundary condition. -/
theorem closed_residue_homs_finite (x : X.left) (hx : IsClosed {x}) :
    Finite (X.left.residueField x ⟶ CommRingCat.of K) := by
  letI : IsClosedImmersion (X.left.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hf : IsFinite (X.left.fromSpecResidueField x≫X.hom) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  let qmap : ℚ →+* X.left.residueField x :=
    (Spec.preimage (X.left.fromSpecResidueField x≫X.hom)).hom
  letI : Algebra ℚ (X.left.residueField x) := qmap.toAlgebra
  have hmap : IsFinite (Spec.map (CommRingCat.ofHom qmap)) := by
    change IsFinite (Spec.map (Spec.preimage (X.left.fromSpecResidueField x≫X.hom)))
    rw [Spec.map_preimage]
    exact hf
  letI : Module.Finite ℚ (X.left.residueField x) := (IsFinite.SpecMap_iff (CommRingCat.ofHom qmap)).mp hmap
  exact Finite.of_injective
    (fun g : X.left.residueField x ⟶ CommRingCat.of K => g.hom.toRatAlgHom)
    (by
      intro f g h
      apply CommRingCat.hom_ext
      exact congrArg AlgHom.toRingHom h)

/-- Actual K-points supported in any finite closed boundary form a finite set. -/
theorem finite_closed_boundary_points (B : Set X.left) (hB : B.Finite) (hBc : IsClosed B) :
    ((pointSupport K (X:=X)) ⁻¹' B).Finite := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hclosed := finite_closed_subset_closedPoints B hB hBc
  letI := hB.fintype
  letI (x : B) : Finite (X.left.residueField x.1 ⟶ CommRingCat.of K) :=
    closed_residue_homs_finite X K x.1 (hclosed x.2)
  let encode : {P : KPoints K X // pointSupport K P∈B} →
      Σ x : B, X.left.residueField x.1 ⟶ CommRingCat.of K := fun P =>
    ⟨⟨pointSupport K P.1,P.2⟩,(Scheme.SpecToEquivOfField K X.left P.1.left).2⟩
  have hinj : Function.Injective encode := by
    intro P Q h
    have he := congrArg
      (fun z : Σ x : B, X.left.residueField x.1 ⟶ CommRingCat.of K =>
        (⟨z.1.1,z.2⟩ : Σ x : X.left, X.left.residueField x ⟶ CommRingCat.of K)) h
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact (Scheme.SpecToEquivOfField K X.left).injective he
  letI : Finite {P : KPoints K X // pointSupport K P∈B} := Finite.of_injective encode hinj
  change Set.Finite {P : KPoints K X | pointSupport K P∈B}
  exact Set.finite_coe_iff.mp (Finite.of_injective encode hinj)

end FourCorner.ThetaLocalSurvival.StrongTopology
