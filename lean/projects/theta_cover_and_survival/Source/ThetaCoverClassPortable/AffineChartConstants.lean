import ThetaCoverClassPortable.SinglePoleChartAlgebra

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicCurve IntermediateField
namespace FourCorner.NativeSinglePoleCharts
universe u
section Constants
variable {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]
  {X : Scheme.{u}} (c : X ⟶ Spec (.of K))
  (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
  (hj : j ≫ c=Spec.map (CommRingCat.ofHom (algebraMap K A)))

include hj in
theorem affine_chart_constants (a : K) :
    (Scheme.ΓSpecIso (.of A)).hom ((j.appIso ⊤).hom
      ((Scheme.TwoAffineOpenCover.algebraOfHom c (j ''ᵁ ⊤)).algebraMap a)) = algebraMap K A a := by
  change (((Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ (j ''ᵁ ⊤) le_top ≫
    (j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (.of A)).hom).hom a)=_
  rw [Scheme.Hom.appIso_hom',← Category.assoc,← Category.assoc]
  rw [Category.assoc (Scheme.ΓSpecIso (.of K)).inv,
    Scheme.Hom.appLE_comp_appLE]
  rw [hj]
  have he : (Spec.map (CommRingCat.ofHom (algebraMap K A))).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop := by
    rw [Scheme.Hom.appLE]
    simp
  rw [he]
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K A))
  rw [← hn]
  simp

end Constants
section Model
variable {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L]
  (t : L) [Fact (t≠0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
  {X : Scheme.{u}} (c : X ⟶ Spec (.of K))
  (i : X ≅ CurveModel.glued K t) (hi : i.hom ≫ CurveModel.gluedToBase K t=c)

include hi in
theorem jZero_over : jZero t i ≫ c=Spec.map (CommRingCat.ofHom
    (algebraMap K (CurveModel.chartRing K ({t}:Set L)))) := by
  rw [jZero,← hi,← Category.assoc,Category.assoc _ i.inv i.hom,i.inv_hom_id,
    Category.comp_id,CurveModel.ι₀_gluedToBase]

include hi in
theorem jInfinity_over : jInfinity t i ≫ c=Spec.map (CommRingCat.ofHom
    (algebraMap K (CurveModel.chartRing K ({t⁻¹}:Set L)))) := by
  rw [jInfinity,← hi,← Category.assoc,Category.assoc _ i.inv i.hom,i.inv_hom_id,
    Category.comp_id,CurveModel.ιInf_gluedToBase]

include hi in
theorem zeroAlgebra_eq_structural : zeroAlgebra t i=Scheme.TwoAffineOpenCover.algebraOfHom c (U t i) := by
  apply Algebra.algebra_ext
  intro a
  apply (zeroSectionsEquiv t i).injective
  change zeroSectionsEquiv t i ((zeroSectionsEquiv t i).symm (algebraMap K _ a)) = _
  rw [(zeroSectionsEquiv t i).apply_symm_apply]
  exact (affine_chart_constants c (jZero t i) (jZero_over t c i hi) a).symm

include hi in
theorem infinityAlgebra_eq_structural : infinityAlgebra t i=Scheme.TwoAffineOpenCover.algebraOfHom c (V t i) := by
  apply Algebra.algebra_ext
  intro a
  apply (infinitySectionsEquiv t i).injective
  change infinitySectionsEquiv t i ((infinitySectionsEquiv t i).symm (algebraMap K _ a)) = _
  rw [(infinitySectionsEquiv t i).apply_symm_apply]
  exact (affine_chart_constants c (jInfinity t i) (jInfinity_over t c i hi) a).symm

end Model
end FourCorner.NativeSinglePoleCharts
