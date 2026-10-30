import OrderedSourceFieldEmbedding
import RationalFieldGeneration
/-! Exact original-cover proposition. X_n remains the independent five-root field
of OrderedSourceFunctionField; S remains the fraction field of the literal original
four-square quotient. The algebra structure below is the proved coordinate embedding. -/
set_option maxHeartbeats 200000
noncomputable section
namespace FourCorner.OriginalCoverCompletion.OrderedSource
open IntermediateField FourCorner.Multiquadratic

def sourceOriginalAlgebra (n : ℚ) (hn : n≠0) : Algebra OriginalFunctionField (sourceField n) :=
  (originalFieldEmbedding n hn).toRingHom.toAlgebra

section
variable (n : ℚ) (hn : n≠0)
/-- The root equation after the actual coordinate-preserving function-field embedding. -/
theorem sourceQ_over_original :
    letI := sourceOriginalAlgebra n hn
    sourceQ n^2=
    algebraMap OriginalFunctionField (sourceField n) (quadraticRadicand n) := by
  letI := sourceOriginalAlgebra n hn
  change sourceQ n^2=originalFieldEmbedding n hn (quadraticRadicand n)
  simp only [quadraticRadicand,tPlus,map_div₀,map_pow,map_sub,map_add,map_mul,map_one,
    originalFieldEmbedding_coordinates,AlgHom.commutes]
  exact sourceQ_literal_square n hn

/-- Equality Q(X_n)=Q(S)(q), with Q(S) acting by the proved literal-coordinate embedding. -/
theorem source_adjoin_q_eq_top :
    letI := sourceOriginalAlgebra n hn
    IntermediateField.adjoin OriginalFunctionField {sourceQ n}=
      (⊤ : IntermediateField OriginalFunctionField (sourceField n)) := by
  letI := sourceOriginalAlgebra n hn
  letI : Module OriginalFunctionField (sourceField n) := (sourceOriginalAlgebra n hn).toModule
  letI : IsScalarTower ℚ OriginalFunctionField (sourceField n) := IsScalarTower.rat
  apply adjoin_top_of_rational_generators (F:=OriginalFunctionField) (originalImage n) (sourceQ n)
    (returnedRootField_eq_top n hn)
  intro i
  exact ⟨fieldCoordinates i,originalFieldEmbedding_coordinates n hn i⟩

/-- Actual vector-space degree of the independent ordered source over the genuine S. -/
theorem source_finrank_over_original :
    letI := sourceOriginalAlgebra n hn
    Module.finrank OriginalFunctionField (sourceField n)=2 := by
  letI := sourceOriginalAlgebra n hn
  have hdim := finrank_adjoin_square_root OriginalFunctionField (sourceQ_over_original n hn)
    (fun u hu => original_radicand_nonsquare n hn ⟨u,by simpa only [sq,quadraticRadicand] using hu.symm⟩)
  rw [source_adjoin_q_eq_top n hn,IntermediateField.finrank_top'] at hdim
  exact hdim

/-- Manuscript prop:ell-original-cover for every nonzero rational parameter (hence
for every positive squarefree integer in the paper), with all six original
coordinates retained and no assumed comparison or dominance premise. -/
theorem prop_ell_original_cover :
    letI := sourceOriginalAlgebra n hn
    (∀i,originalFieldEmbedding n hn (fieldCoordinates i)=originalImage n i) ∧
    sourceQ n^2=((originalImage n 2*originalImage n 5+
      originalImage n 3*originalImage n 4)^2-1)/algebraMap ℚ (sourceField n) n ∧
    IntermediateField.adjoin OriginalFunctionField {sourceQ n}=
      (⊤ : IntermediateField OriginalFunctionField (sourceField n)) ∧
    Module.finrank OriginalFunctionField (sourceField n)=2 :=
  ⟨originalFieldEmbedding_coordinates n hn,sourceQ_literal_square n hn,
    source_adjoin_q_eq_top n hn,source_finrank_over_original n hn⟩

#print axioms prop_ell_original_cover
#print axioms sourceQ_over_original
#print axioms source_adjoin_q_eq_top
#print axioms source_finrank_over_original
end
end FourCorner.OriginalCoverCompletion.OrderedSource
