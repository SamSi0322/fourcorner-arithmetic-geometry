import OrderedSourceGeneration
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
noncomputable section
namespace FourCorner.OriginalCoverCompletion.OrderedSource
open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

/-- The two original position coordinates, as actual elements of the ordered source. -/
def returnedXY (n : ℚ) : Fin 2 → sourceField n := ![originalImage n 0,originalImage n 1]
def positionField (n : ℚ) : IntermediateField ℚ (sourceField n) :=
  IntermediateField.adjoin ℚ (Set.range (returnedXY n))

theorem source_trdeg_lower (n : ℚ) : (2:Cardinal)≤Algebra.trdeg ℚ (sourceField n) := by
  letI : SMul ℚ CoefficientField := (inferInstance : Algebra ℚ CoefficientField).toSMul
  letI : SMul ℚ BaseField := (inferInstance : Algebra ℚ BaseField).toSMul
  letI : SMul CoefficientField BaseField := (inferInstance : Algebra CoefficientField BaseField).toSMul
  letI : SMul ℚ (sourceField n) := (inferInstance : Algebra ℚ (sourceField n)).toSMul
  letI : SMul BaseField (sourceField n) := (inferInstance : Algebra BaseField (sourceField n)).toSMul
  letI : IsScalarTower ℚ CoefficientField BaseField :=
    IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=CoefficientField) (A:=BaseField) (Subsingleton.elim _ _)
  letI : IsScalarTower ℚ BaseField (sourceField n) :=
    IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=BaseField) (A:=sourceField n) (Subsingleton.elim _ _)
  have hc : AlgebraicIndependent ℚ (fun _ : Unit => (RatFunc.X : CoefficientField)) :=
    algebraicIndependent_unique_type_iff.mpr (by convert! RatFunc.transcendental_X (K:=ℚ) using 1; exact Subsingleton.elim _ _)
  have ha : AlgebraicIndependent CoefficientField (fun _ : Unit => (RatFunc.X : BaseField)) :=
    algebraicIndependent_unique_type_iff.mpr RatFunc.transcendental_X
  have hh := hc.sumElim_comp ha
  have hs := hh.map' (f:=IsScalarTower.toAlgHom ℚ BaseField (sourceField n))
    (algebraMap BaseField (sourceField n)).injective
  simpa using hs.cardinalMk_le_trdeg

theorem originalImage_integral_positions (n : ℚ) (hn : n≠0) (i : Fin 6) :
    IsIntegral (positionField n) (originalImage n i) := by
  let K := positionField n
  have hx : originalImage n 0∈K := IntermediateField.subset_adjoin _ _ ⟨0,rfl⟩
  have hy : originalImage n 1∈K := IntermediateField.subset_adjoin _ _ ⟨1,rfl⟩
  have hi {z : sourceField n} (hz : z∈K) : IsIntegral K z := by
    exact isIntegral_algebraMap (R:=K) (x:=(⟨z,hz⟩:K))
  have hxi := hi hx
  have hyi := hi hy
  have h1 : IsIntegral K (1:sourceField n) := isIntegral_one
  fin_cases i
  · exact hxi
  · exact hyi
  all_goals apply IsIntegral.of_pow (n:=2) (by decide)
  · change IsIntegral K (originalImage n 2^2)
    have hh := originalImage_relations n hn 0
    have he : originalImage n 2^2=originalImage n 0^2+originalImage n 1^2 := by
      simp [originalRelations] at hh
      linear_combination hh
    rw [he]; exact (hxi.pow 2).add (hyi.pow 2)
  · change IsIntegral K (originalImage n 3^2)
    have hh := originalImage_relations n hn 1
    have he : originalImage n 3^2=(originalImage n 0-1)^2+originalImage n 1^2 := by
      simp [originalRelations] at hh
      linear_combination hh
    rw [he]; exact ((hxi.sub h1).pow 2).add (hyi.pow 2)
  · change IsIntegral K (originalImage n 4^2)
    have hh := originalImage_relations n hn 2
    have he : originalImage n 4^2=originalImage n 0^2+(originalImage n 1-1)^2 := by
      simp [originalRelations] at hh
      linear_combination hh
    rw [he]; exact (hxi.pow 2).add ((hyi.sub h1).pow 2)
  · change IsIntegral K (originalImage n 5^2)
    have hh := originalImage_relations n hn 3
    have he : originalImage n 5^2=(originalImage n 0-1)^2+(originalImage n 1-1)^2 := by
      simp [originalRelations] at hh
      linear_combination hh
    rw [he]; exact ((hxi.sub h1).pow 2).add ((hyi.sub h1).pow 2)

theorem q_integral_positions (n : ℚ) (hn : n≠0) : IsIntegral (positionField n) (sourceQ n) := by
  apply IsIntegral.of_pow (n:=2) (by decide)
  rw [sourceQ_literal_square n hn]
  have hi := originalImage_integral_positions n hn
  have hnI : IsIntegral (positionField n) (algebraMap ℚ (sourceField n) n) := by
    simpa only [IsScalarTower.algebraMap_apply ℚ (positionField n) (sourceField n)] using
      (isIntegral_algebraMap (R:=positionField n) (x:=algebraMap ℚ (positionField n) n))
  exact ((((hi 2).mul (hi 5)).add ((hi 3).mul (hi 4))).pow 2).sub isIntegral_one |>.mul hnI.inv

/-- The actual source is algebraic over its returned position field. -/
theorem source_algebraic_positions (n : ℚ) (hn : n≠0) :
    Algebra.IsAlgebraic (positionField n) (sourceField n) := by
  have hI (z : sourceField n) : IsIntegral (positionField n) z := by
    have hz : z∈IntermediateField.adjoin ℚ (Set.range (originalImage n)∪{sourceQ n}) := by
      change z∈returnedRootField n
      rw [returnedRootField_eq_top n hn]; trivial
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨i,rfl⟩|hx
      · exact originalImage_integral_positions n hn i
      · rcases Set.mem_singleton_iff.mp hx with rfl; exact q_integral_positions n hn
    | algebraMap r =>
      simpa only [IsScalarTower.algebraMap_apply ℚ (positionField n) (sourceField n)] using
        (isIntegral_algebraMap (R:=positionField n) (x:=algebraMap ℚ (positionField n) r))
    | add x y hx hy ihx ihy => exact ihx.add ihy
    | inv x hx ih => exact ih.inv
    | mul x y hx hy ihx ihy => exact ihx.mul ihy
  exact ⟨fun z => (hI z).isAlgebraic⟩

/-- Dominance is proved, rather than assumed: the returned x,y are algebraically independent. -/
theorem returnedXY_independent (n : ℚ) (hn : n≠0) : AlgebraicIndependent ℚ (returnedXY n) := by
  letI : Algebra.IsAlgebraic (IntermediateField.adjoin ℚ (Set.range (returnedXY n))) (sourceField n) :=
    source_algebraic_positions n hn
  letI : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range (returnedXY n))) (sourceField n) :=
    Algebra.IsAlgebraic.trans _ (IntermediateField.adjoin ℚ (Set.range (returnedXY n))) _
  apply (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℚ (returnedXY n) ?_).1
  simpa using source_trdeg_lower n

#print axioms source_trdeg_lower
#print axioms returnedXY_independent
end FourCorner.OriginalCoverCompletion.OrderedSource
