import ThetaLocalSurvivalPortable.EtaleAffinePointLocalHomeomorph
import ThetaLocalSurvivalPortable.StrongAffineAtlas

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal

variable (K : Type) [NontriviallyNormedField K] [Algebra ℚ K] [CompleteSpace K]

/-- Native scheme etaleness of an actual map of affines gives the analytic local-homeomorphism. -/
theorem affine_scheme_etale_points (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (q : pointObject B ⟶ pointObject A)
    [Etale q.left] [LocallyOfFiniteType (pointObject A).hom] :
    IsLocalHomeomorph (fun P : KPoints K (pointObject B) => P ≫ q) := by
  let h : A →ₐ[ℚ] B := pointToAlgHom A B q
  have hq : pointChange h=q := pointChange_pointToAlgHom A B q
  have hft : (algebraMap ℚ A).FiniteType :=
    HasRingHomProperty.Spec_iff.mp (inferInstance : LocallyOfFiniteType (pointObject A).hom)
  letI : Algebra.FiniteType ℚ A := RingHom.finiteType_algebraMap.mp hft
  letI : Algebra A B := h.toRingHom.toAlgebra
  letI : IsScalarTower ℚ A B := IsScalarTower.of_algebraMap_eq' h.comp_algebraMap.symm
  have het : h.toRingHom.Etale :=
    HasRingHomProperty.Spec_iff.mp (show Etale (pointChange h).left from hq.symm ▸ inferInstance)
  letI : Algebra.Etale A B := het
  have ha := etale_affine_points_localHomeomorph A B K
  have hl := (affineSchemePointsHomeomorph K A).symm.isLocalHomeomorph.comp
    (ha.comp (affineSchemePointsHomeomorph K B).isLocalHomeomorph)
  have he : ((affineSchemePointsHomeomorph K A).symm ∘
      (fun f : B →ₐ[ℚ] K => f.comp (Algebra.algHom ℚ A B)) ∘
        (affineSchemePointsHomeomorph K B)) =
      (fun P : KPoints K (pointObject B) => P ≫ q) := by
    funext P
    change pointChange ((pointToAlgHom B K P).comp h)=P≫q
    rw [←pointChange_comp,pointChange_pointToAlgHom,hq]
  rw [he] at hl
  exact hl

variable {X Y : Over base} (f : X ⟶ Y) [Etale f.left] [LocallyOfFiniteType Y.hom]

/-- Actual compatible affine charts around any actual point of an etale scheme map. -/
theorem etale_compatible_affine_point_charts (P : KPoints K X) :
    ∃ (A B : CommAlgCat ℚ) (jA : pointObject A ⟶ Y) (jB : pointObject B ⟶ X)
      (q : pointObject B ⟶ pointObject A) (Q : KPoints K (pointObject B)),
      IsOpenImmersion jA.left ∧ IsOpenImmersion jB.left ∧ q≫jA=jB≫f ∧
      Etale q.left ∧ LocallyOfFiniteType (pointObject A).hom ∧ Q≫jB=P := by
  obtain ⟨A,jA,pA,hjA,hpA⟩ := exists_affine_chart_through_point K Y (P≫f)
  letI := hjA
  let W : X.left.Opens := f.left ⁻¹ᵁ jA.left.opensRange
  have hxW : pointSupport K P∈W := by
    have h := congrArg (pointSupport K) hpA
    change jA.left (pointSupport K (pointChange pA))=f.left (pointSupport K P) at h
    exact ⟨pointSupport K (pointChange pA),h⟩
  obtain ⟨B,g,hg,hxB,hgW⟩ := Scheme.exists_affine_mem_range_and_range_subset hxW
  let rmap : ℚ →+* B := (Spec.preimage (g≫X.hom)).hom
  letI : Algebra ℚ B := rmap.toAlgebra
  letI : IsOpenImmersion g := hg
  have hb : g≫X.hom=(pointObject B).hom := (Spec.map_preimage (g≫X.hom)).symm
  let jB : pointObject B ⟶ X := Over.homMk g hb
  letI : IsOpenImmersion jB.left := hg
  have hr : Set.range (jB.left≫f.left) ⊆ Set.range jA.left := by
    rintro _ ⟨z,rfl⟩
    exact hgW ⟨z,rfl⟩
  let l := IsOpenImmersion.lift jA.left (jB.left≫f.left) hr
  have hl : l≫jA.left=jB.left≫f.left := IsOpenImmersion.lift_fac _ _ _
  let q : pointObject B ⟶ pointObject A := Over.homMk l (by
    rw [←jA.w,←Category.assoc,hl,Category.assoc,f.w]
    exact jB.w)
  have hq : q≫jA=jB≫f := by apply Over.OverMorphism.ext; exact hl
  letI : Etale (q.left≫jA.left) := by
    change Etale (l≫jA.left)
    rw [hl]
    infer_instance
  have hqe : Etale q.left := Etale.of_comp q.left jA.left
  have hAft : LocallyOfFiniteType (pointObject A).hom := by rw [←jA.w]; infer_instance
  let Q := openPointLift K jB P hxB
  exact ⟨A,CommAlgCat.of ℚ B,jA,jB,q,Q,hjA,hg,hq,hqe,hAft,openPointLift_comp K jB P hxB⟩

/-- Every genuine etale morphism of locally finite-type QQ-schemes induces a local
homeomorphism on actual strong-topology K-points, for every complete normed field K. -/
theorem etale_scheme_points_localHomeomorph :
    IsLocalHomeomorph (fun P : KPoints K X => P≫f) := by
  intro P
  obtain ⟨A,B,jA,jB,q,Q,hjA,hjB,hq,hqe,hAft,hQ⟩ := etale_compatible_affine_point_charts K f P
  letI := hjA
  letI := hjB
  letI := hqe
  letI := hAft
  have hA := (isOpenEmbedding_pointMap K jA).isLocalHomeomorph
  have hB := (isOpenEmbedding_pointMap K jB).isLocalHomeomorph
  have hqL := affine_scheme_etale_points K A B q
  have hC : IsLocalHomeomorph ((fun P : KPoints K X => P≫f) ∘
      (fun Q : KPoints K (pointObject B) => Q≫jB)) := by
    have h := hA.comp hqL
    have he : ((fun P : KPoints K (pointObject A) => P≫jA) ∘
        (fun Q : KPoints K (pointObject B) => Q≫q)) =
        ((fun P : KPoints K X => P≫f) ∘ (fun Q : KPoints K (pointObject B) => Q≫jB)) := by
      funext Q
      dsimp only [Function.comp_apply]
      rw [Category.assoc,hq,←Category.assoc]
    rw [he] at h
    exact h
  have hOn := IsLocalHomeomorphOn.of_comp_right
    (s:=Set.univ) hC.isLocalHomeomorphOn hB.isLocalHomeomorphOn
  exact hOn P ⟨Q,trivial,hQ⟩

end FourCorner.ThetaLocalSurvival.StrongTopology
