import ZeroResidueChart
import InfinityResidueChart
import OriginalChartParameters

noncomputable section
namespace FourCorner.ResidueChartClassification
open AlgebraicCurve AlgebraicCurve.RationalFunctionField RadicalLinearization ResiduePlaceEvaluation LinearizedFactors
variable {k : Type*} [Field k] [NeZero (2:k)] {t κ : k}
local notation "E" => CommonGenus17Field.field k t κ
local instance finiteLine : FiniteDimensional (RatFunc k) E := ResidueRadicalField.finite_over_line k t κ
local instance : DecidableEq (RatFunc k) := Classical.decEq _
attribute [local instance] Classical.propDecidable

/-- Certificates about actual functions, sections, evaluations and valuations
at one chosen place. The root order remains P,C,MZ,BZ,Z. -/
structure FiniteData (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring) : Prop where
  line_image : w.restrict (RatFunc k)=placeOfPoint k (evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩)
  coordinate : ∀ i, (FiniteResidueChart.rootSection t κ hκ w hl i : E)=roots k t κ i
  order : ∀ i, w.ord (roots k t κ i)=if evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=branch t i then 1 else 0
  square : ∀ i, evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl i)^2=
    RadicalLinearization.values t κ⁻¹ (evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩) i
  zero_iff : ∀ i, evaluate w hw (FiniteResidueChart.rootSection t κ hκ w hl i)=0 ↔
    evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=branch t i
  unit_iff : ∀ i, IsUnit (FiniteResidueChart.rootSection t κ hκ w hl i) ↔
    evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠branch t i
  original_coordinate : ∀ ha i,
    (OriginalFiniteChart.originalSection h0 h1 hm hκ w hw hl ha i : E)=Genus17Geometry.fiveRoot t κ i.castSucc
  original_square : ∀ ha i,
    evaluate w hw (OriginalFiniteChart.originalSection h0 h1 hm hκ w hw hl ha i)^2=
      OriginalFiniteChart.values t (evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩)
        (evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩)⁻¹ i
  original_zero_iff : ∀ ha i,
    evaluate w hw (OriginalFiniteChart.originalSection h0 h1 hm hκ w hw hl ha i)=0 ↔
      evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=branch t i.castSucc
  original_unit_iff : ∀ ha i,
    IsUnit (OriginalFiniteChart.originalSection h0 h1 hm hκ w hw hl ha i) ↔
      evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠branch t i.castSucc

/-- Complete actual finite-chart certificate, proved rather than assumed. -/
theorem finite_data (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring) :
    FiniteData h0 h1 hm hκ w hw hl := by
  exact ⟨ResiduePlaceImage.finite_image t κ w hw hl,
    FiniteResidueChart.section_coe t κ hκ w hl,
    FiniteRootData.root_order h0 h1 hm hκ w hw hl,
    FiniteResidueChart.residue_equations t κ hκ w hw hl,
    FiniteRootData.residue_zero_iff h1 hm hκ w hw hl,
    FiniteRootData.unit_iff h1 hm hκ w hw hl,
    fun _ _ => rfl,
    OriginalFiniteChart.residue_equations h0 h1 hm hκ w hw hl,
    OriginalFiniteUnits.residue_zero_iff h0 h1 hm hκ w hw hl,
    OriginalFiniteUnits.unit_iff h0 h1 hm hκ w hw hl⟩

structure InfinityData (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring) : Prop where
  line_image : w.restrict (RatFunc k)=placeInfty k
  parameter_coordinate : (InfinityResidueChart.parameterSection h0 h1 hm hκ w hl : E)=
    (Genus17Geometry.fiveRoot t κ 4)⁻¹
  parameter_order : w.ord (InfinityRootOrders.parameter t κ)=1
  parameter_zero : evaluate w hw (InfinityResidueChart.parameterSection h0 h1 hm hκ w hl)=0
  coordinate : ∀ i, (InfinityResidueChart.rootSection h0 h1 hm hκ w hl i : E)=InfinityRootOrders.normalized t κ i
  order : ∀ i, w.ord (InfinityRootOrders.normalized t κ i)=0
  unit : ∀ i, IsUnit (InfinityResidueChart.rootSection h0 h1 hm hκ w hl i)
  nonzero : ∀ i, evaluate w hw (InfinityResidueChart.rootSection h0 h1 hm hκ w hl i)≠0
  square : ∀ i, evaluate w hw (InfinityResidueChart.rootSection h0 h1 hm hκ w hl i)^2=
    InfinityResidueChart.residueValues t κ i

theorem infinity_data (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring) :
    InfinityData h0 h1 hm hκ w hw hl := by
  have hd := InfinityResidueChart.infinity_chart h0 h1 hm hκ w hw hl
  exact ⟨ResiduePlaceImage.infinity_image t κ w hl,rfl,hd.1,hd.2.1,fun _ => rfl,
    fun i => (hd.2.2 i).1,fun i => (hd.2.2 i).2.1,
    fun i => (hd.2.2 i).2.2.1,fun i => (hd.2.2 i).2.2.2⟩

/-- Exhaustive seven-chart classification of one ACTUAL rational place:
ordinary finite; the five finite branch charts indexed as -T,s,T,-s,0;
or infinity. Every certificate refers to that same w and its evaluation. -/
theorem seven_chart_classification (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational) :
    (∃ hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring,
      FiniteData h0 h1 hm hκ w hw hl ∧
      ((∀ i, evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠branch t i) ∨
        ∃ j, evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=branch t j)) ∨
    (∃ hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring,
      InfinityData h0 h1 hm hκ w hw hl) := by
  by_cases hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring
  · left
    refine ⟨hl,finite_data h0 h1 hm hκ w hw hl,?_⟩
    by_cases hb : ∃ j, evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=branch t j
    · exact Or.inr hb
    · exact Or.inl (by simpa only [not_exists] using hb)
  · exact Or.inr ⟨hl,infinity_data h0 h1 hm hκ w hw hl⟩
end FourCorner.ResidueChartClassification
#print axioms FourCorner.ResidueChartClassification.finite_data
#print axioms FourCorner.ResidueChartClassification.infinity_data
#print axioms FourCorner.ResidueChartClassification.seven_chart_classification
