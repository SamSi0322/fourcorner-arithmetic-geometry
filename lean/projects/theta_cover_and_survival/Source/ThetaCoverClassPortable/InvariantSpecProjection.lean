import ThetaCoverClassPortable.AffineRelationRationalScalars

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FourCorner.ActualAffineQuotient

abbrev relationRing {X R : Scheme.{u}} (s t : R ⟶ X) : Subring Γ(X, ⊤) :=
  s.appTop.hom.eqLocus t.appTop.hom

def inclusion {X R : Scheme.{u}} (s t : R ⟶ X) :
    CommRingCat.of (relationRing s t) ⟶ Γ(X, ⊤) :=
  CommRingCat.ofHom (algebraMap (relationRing s t) Γ(X, ⊤))

/-- Actual map to the Spec of the LITERAL invariant equality subring. -/
def projection {X R : Scheme.{u}} [IsAffine X] (s t : R ⟶ X) :
    X ⟶ Spec (.of (relationRing s t)) :=
  X.isoSpec.hom ≫ Spec.map (inclusion s t)

theorem inclusion_equalizes {X R : Scheme.{u}} (s t : R ⟶ X) :
    inclusion s t ≫ s.appTop = inclusion s t ≫ t.appTop := by
  ext c
  exact c.property

/-- The actual source and target composites with the canonical map agree. -/
theorem projection_coequalizes {X R : Scheme.{u}} [IsAffine X] [IsAffine R]
    (s t : R ⟶ X) : s ≫ projection s t = t ≫ projection s t := by
  simp only [projection, ← Category.assoc, ← Scheme.isoSpec_hom_naturality]
  simp only [Category.assoc, ← Spec.map_comp]
  rw [inclusion_equalizes s t]

/-- Exact structural Gamma comparison: the actual map p pulls functions back
as the SAME invariant inclusion, through the canonical Spec-Gamma isomorphism. -/
theorem projection_appTop {X R : Scheme.{u}} [IsAffine X] (s t : R ⟶ X) :
    (Scheme.ΓSpecIso (.of (relationRing s t))).inv ≫ (projection s t).appTop =
      inclusion s t := by
  simp only [projection, Scheme.Hom.comp_appTop, Scheme.isoSpec, asIso_hom,
    Scheme.toSpecΓ_appTop]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  simp

/-- The actual common affine base map lands in the SAME invariant subring. -/
def invariantBaseMap {S X R : Scheme.{u}} (g : X ⟶ S) (s t : R ⟶ X)
    (hst : s ≫ g = t ≫ g) : Γ(S, ⊤) →+* relationRing s t :=
  g.appTop.hom.codRestrict (relationRing s t) (fun a => by
    change s.appTop.hom (g.appTop.hom a) = t.appTop.hom (g.appTop.hom a)
    have h := congrArg (fun f : R ⟶ S => f.appTop.hom a) hst
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using h)

/-- The quotient's actual structure morphism to its original affine base. -/
def toBase {S X R : Scheme.{u}} [IsAffine S] (g : X ⟶ S) (s t : R ⟶ X)
    (hst : s ≫ g = t ≫ g) : Spec (.of (relationRing s t)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (invariantBaseMap g s t hst)) ≫ S.isoSpec.inv

theorem projection_toBase {S X R : Scheme.{u}} [IsAffine S] [IsAffine X]
    (g : X ⟶ S) (s t : R ⟶ X) (hst : s ≫ g = t ≫ g) :
    projection s t ≫ toBase g s t hst = g := by
  have h : CommRingCat.ofHom (invariantBaseMap g s t hst) ≫ inclusion s t = g.appTop := by
    ext a
    rfl
  simp only [projection, toBase, Category.assoc, ← Spec.map_comp_assoc, h]
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    (Scheme.isoSpec_hom_naturality_assoc g S.isoSpec.inv)

/-- The canonical quotient map preserves the ACTUAL rational structure
constructed on the SAME literal invariant ring. -/
theorem projection_overQQ {X R : Scheme} [IsAffine X]
    (q : X ⟶ Spec (.of ℚ)) (s t : R ⟶ X) (hq : s ≫ q = t ≫ q) :
    letI := FourCorner.AffineRelationRank.invariantRationalAlgebra q s t hq
    projection s t ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (relationRing s t))) = q := by
  letI := FourCorner.AffineRelationRank.invariantRationalAlgebra q s t hq
  let a : CommRingCat.of ℚ ⟶ CommRingCat.of (relationRing s t) :=
    CommRingCat.ofHom (algebraMap ℚ (relationRing s t))
  have h : a ≫ inclusion s t = (Scheme.ΓSpecIso (.of ℚ)).inv ≫ q.appTop := by
    ext k
    change (q.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of ℚ)).inv.hom k) =
      q.appTop.hom ((Scheme.ΓSpecIso (.of ℚ)).inv.hom k)
    rw [FourCorner.AffineRelationRank.appLE_top]
  change projection s t ≫ Spec.map a = q
  calc
    projection s t ≫ Spec.map a = X.isoSpec.hom ≫ Spec.map (a ≫ inclusion s t) := by
      rw [Spec.map_comp, projection, Category.assoc]
    _ = X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of ℚ)).inv ≫ q.appTop) := by rw [h]
    _ = X.toSpecΓ ≫ Spec.map q.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of ℚ)).inv := by
      rw [Spec.map_comp]
      rfl
    _ = q ≫ (Spec (.of ℚ)).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (.of ℚ)).inv :=
      (Scheme.toSpecΓ_naturality_assoc q _).symm
    _ = q := by rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

end FourCorner.ActualAffineQuotient
