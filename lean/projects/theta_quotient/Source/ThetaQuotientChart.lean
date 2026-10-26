import ThetaAmbientChart

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace FourCorner.ThetaQuotientChart
open ThetaAmbientChart
universe u v
variable {K : Type u} [Field K]
variable {ι : Type v}
variable {n : ℕ} [NeZero n] {d : ℕ}
variable (q : ι → ThetaAmbientChart.ambient K n)
variable (hq : ∀ i, (q i).IsHomogeneous d)
variable (j : Fin (n+1))

def homogeneousIdeal : HomogeneousIdeal (ThetaAmbientChart.grading K n) :=
  ⟨Ideal.span (Set.range q), by
    apply Ideal.homogeneous_span
    rintro _ ⟨i,rfl⟩; exact ⟨d, hq i⟩⟩
abbrev Q := ThetaAmbientChart.ambient K n ⧸ (homogeneousIdeal q hq).toIdeal
abbrev G := quotGrading (ThetaAmbientChart.grading K n) (homogeneousIdeal q hq).toIdeal
instance : GradedRing (G q hq) :=
  quotGradingGradedRingOfHomogeneous (ThetaAmbientChart.grading K n) (homogeneousIdeal q hq)
abbrev affineEquation (i : ι) := ThetaAmbientChart.dehom K n j (q i)
abbrev affineIdeal := Ideal.span (Set.range (affineEquation q j))
abbrev affineRing := ThetaAmbientChart.affineAmbient K n ⧸ affineIdeal q j
abbrev quotientMap := quotientGradedMap (ThetaAmbientChart.grading K n) (homogeneousIdeal q hq)
abbrev chartRing := Away (G q hq) ((quotientMap q hq) (X j))

def chartQuotient : ambientAway K n j →+* chartRing q hq j :=
  Away.map (quotientMap q hq) (X j)
lemma chartQuotient_surjective : Function.Surjective (chartQuotient q hq j) :=
  ProjectiveLocalization.away_map_surjective (quotientMap q hq)
    (quotientGradedMap_surjective (ThetaAmbientChart.grading K n) (homogeneousIdeal q hq))
    (Slot02HighProjSpace.X_mem_one K n j)

lemma dehomIdeal : Ideal.map (ThetaAmbientChart.dehom K n j) (homogeneousIdeal q hq).toIdeal = affineIdeal q j := by
  rw [show (homogeneousIdeal q hq).toIdeal = Ideal.span (Set.range q) from rfl,
    Ideal.map_span, ← Set.range_comp]
  rfl

def dehomQuotient : Q q hq →+* affineRing q j :=
  Ideal.quotientMap (affineIdeal q j) (ThetaAmbientChart.dehom K n j)
    ((Ideal.map_le_iff_le_comap).mp (le_of_eq (dehomIdeal q hq j)))
lemma dehomQuotient_T : dehomQuotient q hq j ((quotientMap q hq) (X j)) = 1 := by
  simp [dehomQuotient, quotientMap, quotientGradedMap, Ideal.quotientMap,
    ThetaAmbientChart.dehom]

def chartDehom : chartRing q hq j →+* affineRing q j :=
  (IsLocalization.Away.lift (S := Localization.Away ((quotientMap q hq) (X j)))
    _ (g := dehomQuotient q hq j) (by rw [dehomQuotient_T]; exact isUnit_one)).comp
    (algebraMap _ _)

lemma chartDehom_mk (d : ℕ) (p : Q q hq) (hp : p ∈ G q hq (d • 1)) :
    chartDehom q hq j (Away.mk (G q hq)
      ((quotientMap q hq).map_mem (Slot02HighProjSpace.X_mem_one K n j)) d p hp) =
      dehomQuotient q hq j p := by
  let t := (quotientMap q hq) (X j)
  let l : Localization.Away t →+* affineRing q j :=
    IsLocalization.Away.lift t (g := dehomQuotient q hq j)
      (by rw [dehomQuotient_T]; exact isUnit_one)
  have h : l (Localization.mk p ⟨t ^ d, ⟨d, rfl⟩⟩) *
      l (algebraMap (Q q hq) (Localization.Away t) (t ^ d)) =
      l (algebraMap _ _ p) := by
    rw [← map_mul, Localization.mk_eq_mk', IsLocalization.mk'_spec]
  have ht : dehomQuotient q hq j t = 1 := dehomQuotient_T q hq j
  change l (Localization.mk p ⟨t ^ d, ⟨d, rfl⟩⟩) = dehomQuotient q hq j p
  simpa [l, IsLocalization.Away.lift_eq, ht] using h

lemma dehom_square : (chartDehom q hq j).comp (chartQuotient q hq j) =
    (Ideal.Quotient.mk (affineIdeal q j)).comp (ambientDehom K n j) := by
  apply RingHom.ext
  intro z
  obtain ⟨d,p,hp,rfl⟩ := Away.mk_surjective (ThetaAmbientChart.grading K n)
    (Slot02HighProjSpace.X_mem_one K n j) z
  change chartDehom q hq j (Away.map (quotientMap q hq) _ _) = _
  rw [Away.map_mk]
  have h := chartDehom_mk q hq j d ((quotientMap q hq) p) ((quotientMap q hq).map_mem hp)
  erw [h]
  change dehomQuotient q hq j ((quotientMap q hq) p) =
    Ideal.Quotient.mk (affineIdeal q j) (ambientDehom K n j _)
  rw [ambientDehom_mk K n j]
  rfl

lemma inverse_affineEquation (i : ι) :
    ambientInverse K n j (affineEquation q j i) =
      Away.mk (ThetaAmbientChart.grading K n) (Slot02HighProjSpace.X_mem_one K n j) d
        (q i) (by simpa using ((mem_homogeneousSubmodule d _).mpr (hq i))) := by
  apply (ambientEquiv K n j).injective
  change ambientDehom K n j (ambientInverse K n j _) = ambientDehom K n j _
  have h := RingHom.congr_fun (ambientDehom_inverse K n j) (affineEquation q j i)
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  rw [h, ambientDehom_mk K n j]

lemma chartQuotient_inverse_equation (i : ι) :
    chartQuotient q hq j (ambientInverse K n j (affineEquation q j i)) = 0 := by
  rw [inverse_affineEquation q hq j]
  change Away.map (quotientMap q hq) _ _ = 0
  rw [Away.map_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, val_zero]
  have h : (quotientMap q hq) (q i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  rw [h, Localization.mk_zero]

def chartInverse : affineRing q j →+* chartRing q hq j :=
  Ideal.Quotient.lift (affineIdeal q j) ((chartQuotient q hq j).comp (ambientInverse K n j)) (by
    have h : affineIdeal q j ≤ RingHom.ker ((chartQuotient q hq j).comp (ambientInverse K n j)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact RingHom.mem_ker.mpr (chartQuotient_inverse_equation q hq j i)
    exact fun a ha => h ha)
lemma chartInverse_mk (p : ThetaAmbientChart.affineAmbient K n) :
    chartInverse q hq j (Ideal.Quotient.mk (affineIdeal q j) p) = chartQuotient q hq j (ambientInverse K n j p) := rfl

lemma chartDehom_inverse : (chartDehom q hq j).comp (chartInverse q hq j) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  change chartDehom q hq j (chartInverse q hq j (Ideal.Quotient.mk (affineIdeal q j) p)) = _
  rw [chartInverse_mk]
  have h := RingHom.congr_fun (dehom_square q hq j) (ambientInverse K n j p)
  simp only [RingHom.comp_apply] at h
  rw [h]
  change Ideal.Quotient.mk (affineIdeal q j) (ambientDehom K n j (ambientInverse K n j p)) = _
  have h := RingHom.congr_fun (ambientDehom_inverse K n j) p
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  rw [h]
  rfl
lemma chartInverse_dehom : (chartInverse q hq j).comp (chartDehom q hq j) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := chartQuotient_surjective q hq j x
  change chartInverse q hq j (chartDehom q hq j (chartQuotient q hq j p)) = chartQuotient q hq j p
  have h := RingHom.congr_fun (dehom_square q hq j) p
  simp only [RingHom.comp_apply] at h
  rw [h]
  change chartInverse q hq j (Ideal.Quotient.mk (affineIdeal q j) (ambientDehom K n j p)) = _
  rw [chartInverse_mk]
  have h := RingHom.congr_fun (ambientInverse_dehom K n j) p
  simp only [RingHom.comp_apply, RingHom.id_apply] at h
  rw [h]

def chartEquiv : chartRing q hq j ≃+* affineRing q j :=
  RingEquiv.ofRingHom (chartDehom q hq j) (chartInverse q hq j)
    (chartDehom_inverse q hq j) (chartInverse_dehom q hq j)

def chartSchemeIso :
    (Proj.basicOpen (G q hq) ((quotientMap q hq) (X j))).toScheme ≅
      Spec (.of (affineRing q j)) :=
  Proj.basicOpenIsoSpec (G q hq) _
    ((quotientMap q hq).map_mem (Slot02HighProjSpace.X_mem_one K n j)) one_pos ≪≫
    Scheme.Spec.mapIso ((chartEquiv q hq j).symm.toCommRingCatIso.op)

end FourCorner.ThetaQuotientChart
#print axioms FourCorner.ThetaQuotientChart.chartEquiv
#print axioms FourCorner.ThetaQuotientChart.chartSchemeIso
