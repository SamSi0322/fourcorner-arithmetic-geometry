import ThetaCoverClassPortable.DSinglePoleComplement
import ThetaCoverClassPortable.SinglePoleGenericSections
import ThetaCoverClassPortable.AffineChartConstants

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicCurve IntermediateField
namespace FourCorner.DRationalInputs
open ThetaLiteralModels CurveModel
local instance : IsIntegral curve := integral
local instance : SmoothOfRelativeDimension 1 toBase := smooth
local instance : IsProper toBase := proper
local instance : Algebra ℚ field := constants

/-- Native chart data only. The all-local finite-free fibre condition is deliberately
not a field: it must be proved from these actual finite polynomial maps. -/
structure NativeSinglePoleChartData (m0 : ℕ) where
  generator : field
  poleOrder : ℕ
  generator_ne_zero : generator≠0
  poleOrder_gt : m0<poleOrder
  exact_pole : originPlace.ord generator=-(poleOrder:ℤ)
  regular_away : ∀ v : Place ℚ field, v≠originPlace → 0≤v.ord generator
  transcendental : Transcendental ℚ generator
  fieldFinite : FiniteDimensional ℚ⟮generator⟯ field
  U : curve.Opens
  V : curve.Opens
  f : Γ(curve,U)
  g : Γ(curve,V)
  U_eq_originComplement : U=originComplement
  affine_U : IsAffineOpen U
  affine_V : IsAffineOpen V
  cover : U⊔V=⊤
  generic_U : genericPoint curve∈U
  generic_V : genericPoint curve∈V
  basic_f : curve.basicOpen f=U⊓V
  basic_g : curve.basicOpen g=U⊓V
  reciprocal : (curve.presheaf.map (homOfLE (inf_le_left : U⊓V≤U)).op f) *
    (curve.presheaf.map (homOfLE (inf_le_right : U⊓V≤V)).op g)=1
  finite_f : letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase) U
    (Polynomial.aeval (R:=ℚ) f).toRingHom.Finite
  finite_g : letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase) V
    (Polynomial.aeval (R:=ℚ) g).toRingHom.Finite
  injective_f : letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase) U
    Function.Injective (Polynomial.aeval (R:=ℚ) f)
  native_f : curve.presheaf.germ U (genericPoint curve) generic_U f=generator
  native_g : curve.presheaf.germ V (genericPoint curve) generic_V g=generator⁻¹
  zeroRingEquiv : Γ(curve,U) ≃+* chartRing ℚ ({generator}:Set field)
  zeroRingEquiv_f : zeroRingEquiv f=tChart ℚ generator
  zeroRingEquiv_native : ∀ s : Γ(curve,U),
    curve.presheaf.germ U (genericPoint curve) generic_U s=(zeroRingEquiv s : field)
  zeroRingEquiv_constants : letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase) U
    ∀ a : ℚ, zeroRingEquiv (algebraMap ℚ Γ(curve,U) a)=algebraMap ℚ _ a

/-- Unconditional native charts on the original literal D/Q, for every requested
pole threshold. No FiniteMapData, chart cover or rank is assumed. -/
theorem nonempty_native_singlePole_charts (m0 : ℕ) : Nonempty (NativeSinglePoleChartData m0) := by
  obtain ⟨f,r,hf,hr,hpole,haway,ht,hfd⟩ := single_origin_poles m0
  letI := hfd
  letI : Fact (f≠0) := ⟨hf⟩
  letI : FiniteDimensional ℚ⟮f⁻¹⟯ field := by
    rw [adjoin_simple_inv_eq]
    infer_instance
  obtain ⟨i,hi,hg⟩ := singlePole_model_comparison f ht
  let j : curve ≅ glued ℚ f := i
  have hj : j.hom ≫ gluedToBase ℚ f=toBase := hi
  have hg' : curve.fromSpecStalk (genericPoint curve) ≫ j.hom=
      Spec.map (CommRingCat.ofHom (gluedFunctionFieldEquiv ℚ f).symm.toRingHom) ≫
        (glued ℚ f).fromSpecStalk (genericPoint (glued ℚ f)) := hg
  have hza := NativeSinglePoleCharts.zeroAlgebra_eq_structural f (toBase) j hj
  have hia := NativeSinglePoleCharts.infinityAlgebra_eq_structural f (toBase) j hj
  refine ⟨
    { generator := f
      poleOrder := r
      generator_ne_zero := hf
      poleOrder_gt := hr
      exact_pole := hpole
      regular_away := haway
      transcendental := ht
      fieldFinite := hfd
      U := NativeSinglePoleCharts.U f j
      V := NativeSinglePoleCharts.V f j
      f := NativeSinglePoleCharts.fSection f j
      g := NativeSinglePoleCharts.gSection f j
      U_eq_originComplement := singlePole_U_eq_originComplement f ht j hg' r (by omega) hpole haway
      affine_U := NativeSinglePoleCharts.affine_U f j
      affine_V := NativeSinglePoleCharts.affine_V f j
      cover := NativeSinglePoleCharts.cover f j
      generic_U := NativeSinglePoleCharts.generic_mem_U f j
      generic_V := NativeSinglePoleCharts.generic_mem_V f j
      basic_f := NativeSinglePoleCharts.basicOpen_fSection f j
      basic_g := NativeSinglePoleCharts.basicOpen_gSection f j
      reciprocal := NativeSinglePoleCharts.reciprocal_sections f j hg'
      finite_f := ?_
      finite_g := ?_
      injective_f := ?_
      native_f := ?_
      native_g := ?_
      zeroRingEquiv := NativeSinglePoleCharts.zeroSectionsEquiv f j
      zeroRingEquiv_f := NativeSinglePoleCharts.zeroSectionsEquiv_fSection f j
      zeroRingEquiv_native := NativeSinglePoleCharts.zero_generic_value f j hg'
      zeroRingEquiv_constants := ?_ }⟩
  · rw [← hza]
    exact NativeSinglePoleCharts.finite_aeval_fSection f j
  · rw [← hia]
    exact NativeSinglePoleCharts.finite_aeval_gSection f j
  · rw [← hza]
    exact NativeSinglePoleCharts.injective_aeval_fSection f j ht
  · change curve.germToFunctionField (NativeSinglePoleCharts.U f j) (NativeSinglePoleCharts.fSection f j)=f
    rw [NativeSinglePoleCharts.zero_generic_value f j hg',NativeSinglePoleCharts.zeroSectionsEquiv_fSection]
    rfl
  · change curve.germToFunctionField (NativeSinglePoleCharts.V f j) (NativeSinglePoleCharts.gSection f j)=f⁻¹
    rw [NativeSinglePoleCharts.infinity_generic_value f j hg',NativeSinglePoleCharts.infinitySectionsEquiv_gSection]
    rfl
  · rw [← hza]
    letI := NativeSinglePoleCharts.zeroAlgebra f j
    intro a
    exact (NativeSinglePoleCharts.zeroSectionsAlgEquiv f j).commutes a

def actual_native_singlePole_charts (m0 : ℕ) : NativeSinglePoleChartData m0 :=
  Classical.choice (nonempty_native_singlePole_charts m0)

#print axioms actual_native_singlePole_charts
end FourCorner.DRationalInputs
