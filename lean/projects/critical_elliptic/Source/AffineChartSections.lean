import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.RingTheory.TensorProduct.Maps

/-! Actual sections of a base-compatible affine chart, with their structural
base algebra. No CurveModel or function-field hypotheses are used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
namespace FourCorner.AffineChartSections
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]
variable {X : Scheme.{u}} (c : X ⟶ Spec (.of k)) (U : X.Opens)
variable (e : U.toScheme ≅ Spec (.of R))

/-- This is the actual restriction-to-open global-section isomorphism. -/
lemma topIso_eq_restrictFunctorGamma : U.topIso = (X.restrictFunctorΓ.app (op U)) := by
  rfl

/-- The ring equivalence is assembled from actual section functoriality. -/
def sectionRingIso : Γ(X,U) ≅ CommRingCat.of R :=
  U.topIso.symm ≪≫ Scheme.Γ.mapIso e.symm.op ≪≫ Scheme.ΓSpecIso (.of R)

def sectionRingEquiv : Γ(X,U) ≃+* R :=
  (sectionRingIso U e).commRingCatIsoToRingEquiv

lemma inclusion_sections : U.ι.appTop ≫ U.topIso.hom =
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact (X.presheaf.map_comp _ _).symm.trans
    (congrArg X.presheaf.map (Subsingleton.elim _ _))

lemma structure_sections : (U.ι ≫ c).appTop ≫ U.topIso.hom = c.appLE ⊤ U le_top := by
  rw [Scheme.Hom.comp_appTop, Category.assoc, inclusion_sections]
  change c.app ⊤ ≫ X.presheaf.map (homOfLE (le_top : U ≤ c ⁻¹ᵁ ⊤)).op = _
  rfl

lemma sectionRingIso_constants
    (he : e.inv ≫ U.ι ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k R))) :
    (Scheme.ΓSpecIso (.of k)).inv ≫ c.appLE ⊤ U le_top ≫
      (sectionRingIso U e).hom = CommRingCat.ofHom (algebraMap k R) := by
  rw [← structure_sections c U]
  simp only [sectionRingIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  change (Scheme.ΓSpecIso (.of k)).inv ≫
    (U.ι ≫ c).appTop ≫ e.inv.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom = _
  rw [← Category.assoc (U.ι ≫ c).appTop e.inv.appTop,
    ← Scheme.Hom.comp_appTop, he]
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k R))
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Scalars are forced by the original base morphism and the over-base chart,
not supplied as an extra algebra-compatibility hypothesis. -/
def sectionAlgEquiv
    (he : e.inv ≫ U.ι ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k R))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Γ(X,U) ≃ₐ[k] R := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  refine { sectionRingEquiv U e with commutes' := ?_ }
  intro a
  have h := congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of R => f.hom a)
    (sectionRingIso_constants c U e he)
  exact h

/-- Tensoring the genuine section equivalence preserves the exact scalar
structure used by TwoAffineOpenCover. -/
def tensorSectionsEquiv
    (he : e.inv ≫ U.ι ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (L : Type u) [CommRing L] [Algebra k L] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    L ⊗[k] Γ(X,U) ≃ₐ[k] L ⊗[k] R := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  exact Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[k] L)
    (sectionAlgEquiv c U e he)

/-- A domain after constant extension on the literal affine chart gives the
same domain property for actual structural sections. -/
theorem isDomain_tensor_sections
    (he : e.inv ≫ U.ι ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (L : Type u) [CommRing L] [Algebra k L] [IsDomain (L ⊗[k] R)] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    IsDomain (L ⊗[k] Γ(X,U)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  let f := tensorSectionsEquiv c U e he L
  exact Function.Injective.isDomain f.toRingHom f.injective

end FourCorner.AffineChartSections
#print axioms FourCorner.AffineChartSections.sectionRingIso_constants
#print axioms FourCorner.AffineChartSections.sectionAlgEquiv
#print axioms FourCorner.AffineChartSections.tensorSectionsEquiv
#print axioms FourCorner.AffineChartSections.isDomain_tensor_sections
