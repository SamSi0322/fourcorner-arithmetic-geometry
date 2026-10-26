import ThetaActualQuotient
import ThetaSourceGenus
import ThetaTargetSmooth
noncomputable section
namespace FourCorner.ThetaQuotient
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open ThetaLiteralModels
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An affine-local geometric quotient certificate on the ORIGINAL schemes.
Its invariant-ring universal property and its categorical kernel-pair graphs are
specified on a proved cover of all three actual target charts. -/
structure QuotientCertificate : Prop where
  invariant : ThetaInvolution.sigma (k:=ℚ) ≫ ThetaProjection.projection=ThetaProjection.projection
  cover : ⨆ j : Fin 3,ThetaProjectionChartMap.V j=⊤
  source_cover : ⨆ j : Fin 3,ThetaInvolutionChart.W j=⊤
  original_map : ∀ j : Fin 3,
    (ThetaProjectionChartMap.sourceChartIso j).inv ≫ (ThetaProjectionChartMap.U j).ι ≫ ThetaProjection.projection=
      Spec.map (CommRingCat.ofHom (ThetaChartAlgebras.baseMap j).toRingHom) ≫
        (ThetaProjectionChartMap.targetChartIso j).inv ≫ (ThetaProjectionChartMap.V j).ι
  original_involution : ∀ j : Fin 3,
    (ThetaInvolutionChart.chartIso j).inv ≫ (ThetaInvolutionChart.W j).ι ≫ ThetaInvolution.sigma=
      Spec.map (CommRingCat.ofHom (ThetaInvolutionChart.nn j).toRingHom) ≫
        (ThetaInvolutionChart.chartIso j).inv ≫ (ThetaInvolutionChart.W j).ι
  invariant_map : ∀ (j : Fin 3) (r : ThetaQuotientCharts.R j),
    ((ThetaActualQuotient.invariantIso j r : ThetaActualQuotient.fixedAlgebra j):ThetaQuotientCharts.S j)=
      ThetaChartAlgebras.baseMap j r
  invariant_universal : ∀ (j : Fin 3) (T : Type) [CommRing T] (f : T →+* ThetaQuotientCharts.S j),
    (ThetaInvolutionChart.nn j).toRingHom.comp f=f →
      ∃! g : T →+* ThetaQuotientCharts.R j,(ThetaChartAlgebras.baseMap j).toRingHom.comp g=f
  kernel_pair : ∀ j : Fin 3, Nonempty
    ((Spec (.of (ThetaQuotientCharts.S j)) ⨿ Spec (.of (ThetaQuotientCharts.S j))) ≅
      pullback (ThetaActualQuotient.localProjection j) (ThetaActualQuotient.localProjection j))
  identity_graph_fst : ∀ j : Fin 3,
    coprod.inl ≫ (ThetaActualQuotient.kernelPairSchemeIso j).hom ≫
      pullback.fst (ThetaActualQuotient.localProjection j) (ThetaActualQuotient.localProjection j)=𝟙 _
  identity_graph_snd : ∀ j : Fin 3,
    coprod.inl ≫ (ThetaActualQuotient.kernelPairSchemeIso j).hom ≫
      pullback.snd (ThetaActualQuotient.localProjection j) (ThetaActualQuotient.localProjection j)=𝟙 _
  involution_graph_fst : ∀ j : Fin 3,
    coprod.inr ≫ (ThetaActualQuotient.kernelPairSchemeIso j).hom ≫
      pullback.fst (ThetaActualQuotient.localProjection j) (ThetaActualQuotient.localProjection j)=𝟙 _
  involution_graph_snd : ∀ j : Fin 3,
    coprod.inr ≫ (ThetaActualQuotient.kernelPairSchemeIso j).hom ≫
      pullback.snd (ThetaActualQuotient.localProjection j) (ThetaActualQuotient.localProjection j)=
        Spec.map (CommRingCat.ofHom (ThetaInvolutionChart.nn j).toRingHom)

theorem quotient_certificate : QuotientCertificate where
  invariant:=ThetaDeckInvolution.sigma_projection
  cover:=ThetaProjectionFiniteEtale.target_cover
  source_cover:=ThetaDeckInvolution.source_cover
  original_map:=ThetaProjectionChartMap.chart_square
  original_involution:=ThetaInvolutionChart.chart_sigma
  invariant_map:=ThetaActualQuotient.invariantIso_map
  invariant_universal:=fun j _ _ f hf=>ThetaActualQuotient.invariant_universal j f hf
  kernel_pair:=fun j=>⟨ThetaActualQuotient.kernelPairSchemeIso j⟩
  identity_graph_fst:=ThetaActualQuotient.identity_graph_fst
  identity_graph_snd:=ThetaActualQuotient.identity_graph_snd
  involution_graph_fst:=ThetaActualQuotient.involution_graph_fst
  involution_graph_snd:=ThetaActualQuotient.involution_graph_snd

/-- prop:theta-quotient on the literal projective C,D, actual scheme involution,
actual projection, actual Qbar pullback and actual rational points. The quotient
clause is certified by the affine invariant universal property and categorical
identity/involution kernel-pair decomposition above. There are no hypotheses. -/
theorem prop_theta_quotient :
    IsClosedImmersion (ThetaProjectiveModel.inclusion (sourceEquation ℚ) (source_homogeneous ℚ)) ∧
    IsIntegral (C ℚ) ∧ IsProper (cToBase ℚ) ∧ SmoothOfRelativeDimension 1 (cToBase ℚ) ∧
    GeometricallyConnected (cToBase ℚ) ∧
    (letI := ThetaSourceGenus.geometric_integral
     letI := (baseToFunctionField ThetaSourceGenus.geometricToBase).toAlgebra
     genusFF (AlgebraicClosure ℚ) ThetaSourceGenus.geometricScheme.functionField=5) ∧
    Nat.card (ThetaBoundary.RationalBoundary (k:=ℚ))=8 ∧
    IsClosedImmersion (ThetaProjectiveModel.inclusion (targetEquation ℚ) (target_homogeneous ℚ)) ∧
    IsProper (dToBase ℚ) ∧ SmoothOfRelativeDimension 1 (dToBase ℚ) ∧
    ThetaInvolution.sigma (k:=ℚ) ≫ ThetaInvolution.sigma=𝟙 _ ∧
    (∀ (K : Type) [Field K] (x : Spec (.of K) ⟶ C ℚ), x ≫ ThetaInvolution.sigma≠x) ∧
    QuotientCertificate ∧ IsFinite (ThetaProjection.projection (k:=ℚ)) ∧
    Etale (ThetaProjection.projection (k:=ℚ)) ∧
    (∀ y : D ℚ,(ThetaProjection.projection (k:=ℚ)).finrank y=2) ∧
    Surjective (ThetaProjection.projection (k:=ℚ)) ∧
    ThetaActualPoints.originC (k:=ℚ) ≫ cToBase ℚ=𝟙 _ ∧
    ThetaActualPoints.originD (k:=ℚ) ≫ dToBase ℚ=𝟙 _ ∧
    ThetaActualPoints.originC (k:=ℚ) ≫ ThetaProjection.projection=ThetaActualPoints.originD :=
  ⟨c_closed ℚ,ThetaSourceComparison.source_integral,c_proper ℚ,ThetaSourceSmooth.source_smooth,
    ThetaSourceGenus.source_connected,ThetaSourceGenus.genus_five,ThetaBoundary.rational_boundary_card,
    d_closed ℚ,d_proper ℚ,ThetaTargetSmooth.target_smooth,ThetaInvolution.sigma_sq,
    fun K _ x hx=>ThetaDeckInvolution.no_fixed_point K x hx,quotient_certificate,
    ThetaProjectionFiniteEtale.projection_finite,ThetaProjectionFiniteEtale.projection_etale,
    ThetaProjectionDegree.projection_degree_two,ThetaProjectionDegree.projection_surjective,
    ThetaActualPoints.boundaryPoint_over (fun _=>true),ThetaActualPoints.originD_over,
    ThetaOriginImage.origin_image⟩
end FourCorner.ThetaQuotient
#print axioms FourCorner.ThetaQuotient.quotient_certificate
#print axioms FourCorner.ThetaQuotient.prop_theta_quotient
