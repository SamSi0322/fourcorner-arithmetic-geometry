import ThetaCoverClassPortable.ThetaProjectionChartMap
import ThetaCoverClassPortable.ThetaChartFiniteEtale
noncomputable section
namespace FourCorner.ThetaProjectionFiniteEtale
open AlgebraicGeometry CategoryTheory
open ThetaProjectionChartMap
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma local_map (j : Fin 3) :
    (sourceChartIso j).inv ≫ (ThetaProjection.projection ∣_ V j) ≫ (targetChartIso j).hom=
      Spec.map (CommRingCat.ofHom (ThetaChartAlgebras.baseMap j).toRingHom) := by
  let v:=(targetChartIso j).inv ≫ (V j).ι
  apply (cancel_mono v).mp
  have h:=chart_square j
  simp only [v,Category.assoc,Iso.hom_inv_id_assoc,morphismRestrict_ι]
  change (sourceChartIso j).inv ≫ (U j).ι ≫ ThetaProjection.projection=
    Spec.map (CommRingCat.ofHom (ThetaChartAlgebras.baseMap j).toRingHom) ≫ (targetChartIso j).inv ≫ (V j).ι
  exact h
lemma local_property (P : MorphismProperty Scheme) [MorphismProperty.RespectsIso P]
    (j : Fin 3) (h : P (Spec.map (CommRingCat.ofHom (ThetaChartAlgebras.baseMap j).toRingHom))) :
    P (ThetaProjection.projection ∣_ V j) := by
  rw [←local_map] at h
  have h1 : P ((ThetaProjection.projection ∣_ V j) ≫ (targetChartIso j).hom) :=
    (MorphismProperty.cancel_left_of_respectsIso P (sourceChartIso j).inv _).mp h
  exact (MorphismProperty.cancel_right_of_respectsIso P _ (targetChartIso j).hom).mp h1
lemma targetIndex_surjective : Function.Surjective ThetaQuotientCharts.targetIndex := by
  intro j
  fin_cases j
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨0,rfl⟩
lemma target_cover : ⨆ j : Fin 3,V j=⊤ := by
  have h:=ThetaProjectiveModel.opens_cover (ThetaLiteralModels.targetEquation ℚ) (ThetaLiteralModels.target_homogeneous ℚ)
  change (⨆ i : Fin 3,Proj.basicOpen dg (qmD (MvPolynomial.X i)))=⊤ at h
  rw [←h]
  apply le_antisymm
  · apply iSup_le
    intro j
    exact le_iSup (fun i : Fin 3=>Proj.basicOpen dg (qmD (MvPolynomial.X i))) (ThetaQuotientCharts.targetIndex j)
  · apply iSup_le
    intro i
    obtain ⟨j,rfl⟩:=targetIndex_surjective i
    exact le_iSup V j
/-- Native finiteness of the original global [Q:R:P] morphism, proved on all target charts. -/
theorem projection_finite : IsFinite (ThetaProjection.projection (k:=ℚ)) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P:=@IsFinite) V target_cover
  intro j
  exact local_property @IsFinite j (ThetaChartFiniteEtale.spec_finite j)
/-- Native etaleness of the original global [Q:R:P] morphism, including P=0. -/
theorem projection_etale : Etale (ThetaProjection.projection (k:=ℚ)) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P:=@Etale) V target_cover
  intro j
  exact local_property @Etale j (ThetaChartFiniteEtale.spec_etale j)
end FourCorner.ThetaProjectionFiniteEtale
#print axioms FourCorner.ThetaProjectionFiniteEtale.projection_finite
#print axioms FourCorner.ThetaProjectionFiniteEtale.projection_etale
