import ThetaLocalSurvivalPortable.FiniteEtaleAffineCovering

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal

variable (K : Type) [NontriviallyNormedField K] [Algebra ℚ K] [CompleteSpace K] [ProperSpace K]

/-- Covering-map theorem for genuine finite etale scheme maps of QQ-affines. -/
theorem finite_etale_affine_scheme_points_covering (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (q : pointObject B ⟶ pointObject A)
    [IsFinite q.left] [Etale q.left] [LocallyOfFiniteType (pointObject A).hom] :
    IsCoveringMap (fun P : KPoints K (pointObject B) => P ≫ q) := by
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
  have hfinite : h.toRingHom.Finite :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom h.toRingHom)).mp
      (show IsFinite (pointChange h).left from hq.symm ▸ inferInstance)
  letI : Module.Finite A B := hfinite
  have ha := finite_etale_affine_points_covering A B K
  have hl := (ha.comp_homeomorph (affineSchemePointsHomeomorph K B)).homeomorph_comp
    (affineSchemePointsHomeomorph K A).symm
  have he : ((affineSchemePointsHomeomorph K A).symm ∘
      (fun f : B →ₐ[ℚ] K => f.comp (Algebra.algHom ℚ A B)) ∘
        (affineSchemePointsHomeomorph K B)) =
      (fun P : KPoints K (pointObject B) => P ≫ q) := by
    funext P
    change pointChange ((pointToAlgHom B K P).comp h)=P≫q
    rw [←pointChange_comp,pointChange_pointToAlgHom,hq]
  rw [he] at hl
  exact hl

end FourCorner.ThetaLocalSurvival.StrongTopology
