import Slot02HighChart

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace FourCorner.GenericFiveChart
open OppositeProjective.HighChart
universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {ι : Type v}
variable (q : ι → OppositeHomogeneousQuadrics.Ambient K)
variable (hq : ∀ i, (q i).IsHomogeneous 2)

def homogeneousIdeal : HomogeneousIdeal (OppositeProjective.grading K) :=
  ⟨Ideal.span (Set.range q), by
    apply Ideal.homogeneous_span
    rintro _ ⟨i,rfl⟩; exact ⟨2, hq i⟩⟩
abbrev Q := OppositeHomogeneousQuadrics.Ambient K ⧸ (homogeneousIdeal q hq).toIdeal
abbrev G := quotGrading (OppositeProjective.grading K) (homogeneousIdeal q hq).toIdeal
instance : GradedRing (G q hq) :=
  quotGradingGradedRingOfHomogeneous (OppositeProjective.grading K) (homogeneousIdeal q hq)
abbrev affineEquation (i : ι) := OppositeHomogeneousQuadrics.dehomT (q i)
abbrev affineIdeal := Ideal.span (Set.range (affineEquation q))
abbrev affineRing := OppositeHomogeneousQuadrics.AffineAmbient K ⧸ affineIdeal q
abbrev quotientMap := quotientGradedMap (OppositeProjective.grading K) (homogeneousIdeal q hq)
abbrev chartRing := Away (G q hq) ((quotientMap q hq) (X (4 : Fin 5)))

def chartQuotient : ambientAway (K := K) →+* chartRing q hq :=
  Away.map (quotientMap q hq) (X (4 : Fin 5))
lemma chartQuotient_surjective : Function.Surjective (chartQuotient q hq) :=
  ProjectiveLocalization.away_map_surjective (quotientMap q hq)
    (quotientGradedMap_surjective (OppositeProjective.grading K) (homogeneousIdeal q hq))
    (Slot02HighProjSpace.X_mem_one K 4 4)

lemma dehomIdeal : Ideal.map OppositeHomogeneousQuadrics.dehomT (homogeneousIdeal q hq).toIdeal = affineIdeal q := by
  rw [show (homogeneousIdeal q hq).toIdeal = Ideal.span (Set.range q) from rfl,
    Ideal.map_span, ← Set.range_comp]
  rfl

def dehomQuotient : Q q hq →+* affineRing q :=
  Ideal.quotientMap (affineIdeal q) OppositeHomogeneousQuadrics.dehomT
    ((Ideal.map_le_iff_le_comap).mp (le_of_eq (dehomIdeal q hq)))
lemma dehomQuotient_T : dehomQuotient q hq ((quotientMap q hq) (X (4 : Fin 5))) = 1 := by
  simp [dehomQuotient, quotientMap, quotientGradedMap, Ideal.quotientMap,
    OppositeHomogeneousQuadrics.dehomT]

def chartDehom : chartRing q hq →+* affineRing q :=
  (IsLocalization.Away.lift (S := Localization.Away ((quotientMap q hq) (X (4 : Fin 5))))
    _ (g := dehomQuotient q hq) (by rw [dehomQuotient_T]; exact isUnit_one)).comp
    (algebraMap _ _)

lemma chartDehom_mk (d : ℕ) (p : Q q hq) (hp : p ∈ G q hq (d • 1)) :
    chartDehom q hq (Away.mk (G q hq)
      ((quotientMap q hq).map_mem (Slot02HighProjSpace.X_mem_one K 4 4)) d p hp) =
      dehomQuotient q hq p := by
  let t := (quotientMap q hq) (X (4 : Fin 5))
  let l : Localization.Away t →+* affineRing q :=
    IsLocalization.Away.lift t (g := dehomQuotient q hq)
      (by rw [dehomQuotient_T]; exact isUnit_one)
  have h : l (Localization.mk p ⟨t ^ d, ⟨d, rfl⟩⟩) *
      l (algebraMap (Q q hq) (Localization.Away t) (t ^ d)) =
      l (algebraMap _ _ p) := by
    rw [← map_mul, Localization.mk_eq_mk', IsLocalization.mk'_spec]
  have ht : dehomQuotient q hq t = 1 := dehomQuotient_T q hq
  change l (Localization.mk p ⟨t ^ d, ⟨d, rfl⟩⟩) = dehomQuotient q hq p
  simpa [l, IsLocalization.Away.lift_eq, ht] using h

lemma dehom_square : (chartDehom q hq).comp (chartQuotient q hq) =
    (Ideal.Quotient.mk (affineIdeal q)).comp ambientDehom := by
  apply RingHom.ext
  intro z
  obtain ⟨d,p,hp,rfl⟩ := Away.mk_surjective (OppositeProjective.grading K)
    (Slot02HighProjSpace.X_mem_one K 4 4) z
  change chartDehom q hq (Away.map (quotientMap q hq) _ _) = _
  rw [Away.map_mk]
  have h := chartDehom_mk q hq d ((quotientMap q hq) p) ((quotientMap q hq).map_mem hp)
  erw [h]
  change dehomQuotient q hq ((quotientMap q hq) p) =
    Ideal.Quotient.mk (affineIdeal q) (ambientDehom _)
  rw [ambientDehom_mk]
  rfl

lemma inverse_affineEquation (i : ι) :
    ambientInverse (affineEquation q i) =
      Away.mk (OppositeProjective.grading K) (Slot02HighProjSpace.X_mem_one K 4 4) 2
        (q i) (by simpa using ((mem_homogeneousSubmodule 2 _).mpr (hq i))) := by
  apply (ambientEquiv (K := K)).injective
  change ambientDehom (ambientInverse _) = ambientDehom _
  have h := RingHom.congr_fun (ambientDehom_inverse (K := K)) (affineEquation q i)
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  rw [h, ambientDehom_mk]

lemma chartQuotient_inverse_equation (i : ι) :
    chartQuotient q hq (ambientInverse (affineEquation q i)) = 0 := by
  rw [inverse_affineEquation q hq]
  change Away.map (quotientMap q hq) _ _ = 0
  rw [Away.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, val_zero]
  have h : (quotientMap q hq) (q i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  rw [h, Localization.mk_zero]

def chartInverse : affineRing q →+* chartRing q hq :=
  Ideal.Quotient.lift (affineIdeal q) ((chartQuotient q hq).comp ambientInverse) (by
    have h : affineIdeal q ≤ RingHom.ker ((chartQuotient q hq).comp ambientInverse) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact RingHom.mem_ker.mpr (chartQuotient_inverse_equation q hq i)
    exact fun a ha => h ha)
lemma chartInverse_mk (p : OppositeHomogeneousQuadrics.AffineAmbient K) :
    chartInverse q hq (Ideal.Quotient.mk (affineIdeal q) p) = chartQuotient q hq (ambientInverse p) := rfl

lemma chartDehom_inverse : (chartDehom q hq).comp (chartInverse q hq) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  change chartDehom q hq (chartInverse q hq (Ideal.Quotient.mk (affineIdeal q) p)) = _
  rw [chartInverse_mk]
  have h := RingHom.congr_fun (dehom_square q hq) (ambientInverse p)
  simp only [RingHom.comp_apply] at h
  rw [h]
  change Ideal.Quotient.mk (affineIdeal q) (ambientDehom (ambientInverse p)) = _
  have h := RingHom.congr_fun (ambientDehom_inverse (K := K)) p
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  rw [h]
  rfl
lemma chartInverse_dehom : (chartInverse q hq).comp (chartDehom q hq) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := chartQuotient_surjective q hq x
  change chartInverse q hq (chartDehom q hq (chartQuotient q hq p)) = chartQuotient q hq p
  have h := RingHom.congr_fun (dehom_square q hq) p
  simp only [RingHom.comp_apply] at h
  rw [h]
  change chartInverse q hq (Ideal.Quotient.mk (affineIdeal q) (ambientDehom p)) = _
  rw [chartInverse_mk]
  have h := RingHom.congr_fun (ambientInverse_dehom (K := K)) p
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  rw [h]

def chartEquiv : chartRing q hq ≃+* affineRing q :=
  RingEquiv.ofRingHom (chartDehom q hq) (chartInverse q hq)
    (chartDehom_inverse q hq) (chartInverse_dehom q hq)

def chartSchemeIso :
    (Proj.basicOpen (G q hq) ((quotientMap q hq) (X (4 : Fin 5)))).toScheme ≅
      Spec (.of (affineRing q)) :=
  Proj.basicOpenIsoSpec (G q hq) _
    ((quotientMap q hq).map_mem (Slot02HighProjSpace.X_mem_one K 4 4)) one_pos ≪≫
    Scheme.Spec.mapIso ((chartEquiv q hq).symm.toCommRingCatIso.op)

end FourCorner.GenericFiveChart
#print axioms FourCorner.GenericFiveChart.chartEquiv
#print axioms FourCorner.GenericFiveChart.chartSchemeIso
