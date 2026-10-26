import CriticalSchemeIso
import CriticalGeometricConnected
import CriticalBoundaryClassification
import CriticalBoundaryCardinality

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace FourCorner.CriticalEllipticFull
open CriticalProj23 CriticalSignPoints CriticalBoundaryCardinality
variable {k : Type u} [Field k]

theorem unique_geometric_boundary (i : k) (h2 : (2:k)≠0)
    (L : Type u) [Field L] [Algebra k L]
    (p : Spec (.of L) ⟶ criticalCurve i)
    (hp : p ≫ criticalToSpec i = Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    p ⁻¹ᵁ CriticalHomogeneousEvaluation.shiftOpen i = ⊥ ↔
      ∃! e : Fin 3 → Bool, p = pointOver (L:=L) i e := by
  constructor
  · intro hb
    obtain ⟨e,he⟩ := (CriticalBoundaryClassification.geometric_boundary i p hp).mp hb
    refine ⟨e,he,?_⟩
    intro d hd
    apply pointOver_injective (L:=L) i h2
    exact hd.symm.trans he
  · rintro ⟨e,he,_⟩
    exact (CriticalBoundaryClassification.geometric_boundary i p hp).mpr ⟨e,he⟩

/-- Complete statement of prop:crit-elliptic on the ORIGINAL projective
two-quadric scheme. The independent elliptic target has the literal native
affine coordinate ring y²=x³−x. Boundary completeness holds after every field
extension with the original structure map, with exact Scheme-point equality. -/
theorem critical_elliptic (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    SmoothOfRelativeDimension 1 (criticalToSpec i) ∧
    GeometricallyConnected (criticalToSpec i) ∧
    (∃ f : criticalCurve i ≅ EllipticQuarticModel.curve k,
      f.hom ≫ EllipticQuarticModel.toBase k = criticalToSpec i) ∧
    (∀ (L : Type u) [Field L] [Algebra k L]
      (p : Spec (.of L) ⟶ criticalCurve i),
      p ≫ criticalToSpec i = Spec.map (CommRingCat.ofHom (algebraMap k L)) →
      (p ⁻¹ᵁ CriticalHomogeneousEvaluation.shiftOpen i = ⊥ ↔
        ∃! e : Fin 3 → Bool, p = pointOver (L:=L) i e)) ∧
    (∀ (L : Type u) [Field L] [Algebra k L],
      Nat.card (Set.range (pointOver (L:=L) i)) = 8) ∧
    Nat.card (Set.range (point i)) = 8 := by
  refine ⟨CriticalProjectiveSmooth.projective_smooth i hi h2,
    CriticalGeometricConnected.geometricallyConnected i hi h2,
    ⟨CriticalSchemeIso.iso i hi h2,CriticalSchemeIso.iso_over_base i hi h2⟩,
    ?_,?_,point_card i h2⟩
  · intro L _ _ p hp
    exact unique_geometric_boundary i h2 L p hp
  · intro L _ _
    exact pointOver_card (L:=L) i h2

end FourCorner.CriticalEllipticFull
#print axioms FourCorner.CriticalEllipticFull.unique_geometric_boundary
#print axioms FourCorner.CriticalEllipticFull.critical_elliptic
