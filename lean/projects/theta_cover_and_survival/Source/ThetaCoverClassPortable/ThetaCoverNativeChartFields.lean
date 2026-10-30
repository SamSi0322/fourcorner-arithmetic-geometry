import ThetaCoverClassPortable.ActualAffineChartFunctionField
import ThetaCoverClassPortable.ThetaCoverRationalData
import ThetaCoverClassPortable.ThetaProjectionChartMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
namespace FourCorner.ThetaCoverNativeChartFields
open ThetaLiteralModels ThetaQuotientCharts ThetaProjectionChartMap
open ThetaDNativeProjRatios ThetaDPlaneChartSections ActualAffineChartFunctionField
local instance : IsIntegral (C ℚ) := ThetaSourceComparison.source_integral
local instance : IsIntegral (D ℚ) := ThetaDPlaneChartSections.original_integral
local instance : Surjective (ThetaProjection.projection (k:=ℚ)) := ThetaProjectionDegree.projection_surjective

abbrev R0 := ThetaQuotientCharts.R 0
abbrev S0 := ThetaQuotientCharts.S 0

def sourceChart : Spec (.of S0) ⟶ C ℚ :=
  (ThetaProjectionChartMap.sourceChartIso 0).inv ≫ (ThetaProjectionChartMap.U 0).ι

def targetChart : Spec (.of R0) ⟶ D ℚ :=
  (ThetaProjectionChartMap.targetChartIso 0).inv ≫ (ThetaProjectionChartMap.V 0).ι

local instance : IsOpenImmersion sourceChart := by unfold sourceChart;infer_instance
local instance : IsOpenImmersion targetChart := by unfold targetChart;infer_instance

 theorem target_open_nonempty : Nonempty (ThetaProjectionChartMap.V 0) := by
  exact ThetaDNativeProjRatios.basic_nonempty 2

 theorem source_open_nonempty : Nonempty (ThetaProjectionChartMap.U 0) := by
  obtain ⟨y⟩ := target_open_nonempty
  obtain ⟨x,hx⟩ := (ThetaProjection.projection (k:=ℚ)).surjective y.val
  refine ⟨⟨x,?_⟩⟩
  change ThetaProjection.projection x∈ThetaProjectionChartMap.V 0
  rw [hx]
  exact y.property

local instance : Nonempty (Spec (.of S0)) := by
  obtain ⟨x⟩ := source_open_nonempty
  exact ⟨(ThetaProjectionChartMap.sourceChartIso 0).hom x⟩
local instance : Nonempty (Spec (.of R0)) := by
  obtain ⟨x⟩ := target_open_nonempty
  exact ⟨(ThetaProjectionChartMap.targetChartIso 0).hom x⟩

 theorem source_domain : IsDomain S0 :=
  (affine_isIntegral_iff (.of S0)).mp (isIntegral_of_isOpenImmersion sourceChart)
 theorem target_domain : IsDomain R0 :=
  (affine_isIntegral_iff (.of R0)).mp (isIntegral_of_isOpenImmersion targetChart)
local instance : IsDomain S0 := source_domain
local instance : IsDomain R0 := target_domain

abbrev sourceField := (C ℚ).functionField
abbrev targetField := (D ℚ).functionField

def sourceMap : S0 →+* sourceField := ActualAffineChartFunctionField.chartMap sourceChart
def targetMap : R0 →+* targetField := ActualAffineChartFunctionField.chartMap targetChart
local instance : Algebra S0 sourceField := sourceMap.toAlgebra
local instance : Algebra R0 targetField := targetMap.toAlgebra

 theorem source_fractionRing : IsFractionRing S0 sourceField :=
  ActualAffineChartFunctionField.chart_fractionRing sourceChart
 theorem target_fractionRing : IsFractionRing R0 targetField :=
  ActualAffineChartFunctionField.chart_fractionRing targetChart

 theorem source_generic_diagram : Spec.map (CommRingCat.ofHom sourceMap) ≫ sourceChart=
    (C ℚ).fromSpecStalk (genericPoint (C ℚ)) :=
  ActualAffineChartFunctionField.chart_diagram sourceChart
 theorem target_generic_diagram : Spec.map (CommRingCat.ofHom targetMap) ≫ targetChart=
    (D ℚ).fromSpecStalk (genericPoint (D ℚ)) :=
  ActualAffineChartFunctionField.chart_diagram targetChart

 theorem actual_relative_field_square :
    (ThetaNativeFunctionFieldMap.fieldMap (ThetaProjection.projection (k:=ℚ))).comp targetMap=
      sourceMap.comp (ThetaChartAlgebras.baseMap 0).toRingHom :=
  ActualAffineChartFunctionField.square_field_comm sourceChart (ThetaProjection.projection (k:=ℚ))
    targetChart (ThetaChartAlgebras.baseMap 0).toRingHom (ThetaProjectionChartMap.chart_square 0)

local instance : Nonempty (ThetaDNativeProjRatios.B 2) := ThetaDNativeProjRatios.basic_nonempty 2
local instance : Algebra ℚ targetField := (baseToFunctionField (dToBase ℚ)).toAlgebra
local instance : CharZero targetField := charZero_of_injective_algebraMap (algebraMap ℚ targetField).injective

 theorem targetMap_X (a : Fin 2) : targetMap (Ideal.Quotient.mk _ (MvPolynomial.X a))=
    ThetaDNativeProjRatios.ratio 2 (ThetaAmbientChart.insert 2 2 a) := by
  calc
    targetMap (Ideal.Quotient.mk _ (MvPolynomial.X a))=
        (D ℚ).germToFunctionField (ThetaDNativeProjRatios.B 2)
          (ThetaDNativeProjSections.sections 2 (Ideal.Quotient.mk _ (MvPolynomial.X a))) := by
      apply ActualAffineChartFunctionField.chartMap_of_section targetChart
        (ThetaDNativeProjRatios.B 2) (ThetaDOriginalChartOpens.chart_into_basic 2)
      exact congrArg (fun f : CommRingCat.of R0 ⟶ Γ(Spec (.of R0),⊤)=>
        f.hom (Ideal.Quotient.mk _ (MvPolynomial.X a))) (ThetaDOriginalChartOpens.chart_section_appLE 2)
    _=ThetaDNativeProjRatios.ratio 2 (ThetaAmbientChart.insert 2 2 a) :=
      ThetaDNativeProjSections.sections_coordinate_generic 2 a

 theorem actual_b_is_rationalH : targetMap (ThetaQuotientCharts.b 0)=ThetaCoverRationalData.rationalH := by
  have hx : targetMap (Ideal.Quotient.mk _ (MvPolynomial.X (0:Fin 2)))=ThetaDNativeProjRatios.ratio 2 0 := targetMap_X 0
  have hy : targetMap (Ideal.Quotient.mk _ (MvPolynomial.X (1:Fin 2)))=ThetaDNativeProjRatios.ratio 2 1 := targetMap_X 1
  have hc : targetMap (Ideal.Quotient.mk _ (MvPolynomial.C (1/2:ℚ)))=(1/2:targetField) := by
    have hh := RingHom.congr_fun (Subsingleton.elim (targetMap.comp (algebraMap ℚ R0))
      (algebraMap ℚ targetField)) (1/2)
    change targetMap (Ideal.Quotient.mk _ (MvPolynomial.C (1/2:ℚ)))=algebraMap ℚ targetField (1/2) at hh
    exact hh.trans (by norm_num)
  unfold ThetaQuotientCharts.b ThetaQuotientCharts.bpoly ThetaQuotientCharts.rcoords ThetaQuotientCharts.rq
  simp only [Ideal.Quotient.mkₐ_eq_mk,map_mul,map_add,map_sub,map_pow,map_one,map_ofNat,hx,hy,hc]
  unfold ThetaCoverRationalData.rationalH
  ring

#print axioms source_domain
#print axioms source_generic_diagram
end FourCorner.ThetaCoverNativeChartFields
