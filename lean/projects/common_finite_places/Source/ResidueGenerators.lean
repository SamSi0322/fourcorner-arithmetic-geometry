import ResidueRadicalDegree
import Genus17Generators

noncomputable section
namespace FourCorner.ResidueGenerators
open IntermediateField Genus17Geometry
variable (K : Type*) [Field K]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

theorem four_root_generates (t : K) :
    Algebra.adjoin (RatFunc K) (Set.range (CommonLiteralField.root K t)) = ⊤ := by
  letI := ResidueRadicalField.four_finite K t
  apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic (fun x _ =>
    (IsIntegral.of_finite (RatFunc K) x).isAlgebraic)).mp
  exact CommonLiteralField.root_adjoin_eq_top K t

theorem fifth_root_generates (t κ : K) :
    Algebra.adjoin (CommonLiteralField.field K t) {fifthRoot t κ} = ⊤ := by
  letI := ResidueRadicalField.fifth_finite K t κ
  apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic (fun x _ =>
    (IsIntegral.of_finite (CommonLiteralField.field K t) x).isAlgebraic)).mp
  apply IntermediateField.lift_injective (CommonGenus17Field.field K t κ)
  rw [IntermediateField.lift_adjoin_simple,IntermediateField.lift_top]
  rfl

theorem fiveRoot_sq (t κ : K) (i : Fin 5) : fiveRoot t κ i ^ 2 =
    algebraMap (RatFunc K) (CommonGenus17Field.field K t κ) (CommonFiveIndependence.value t κ i) := by
  fin_cases i
  all_goals simp only [fiveRoot,orderedRoot,CommonFiveIndependence.value]
  all_goals first
    | rw [← map_pow,CommonLiteralField.root_sq]
      rfl
    | apply Subtype.ext
      exact ResidueRadicalField.fifth_radical_sq K t κ

/-- The five separately named literal radicals generate the actual residue
function field in every characteristic. -/
theorem fiveRoot_generates (t κ : K) :
    Algebra.adjoin (RatFunc K) (Set.range (fiveRoot t κ)) = ⊤ := by
  let S := Algebra.adjoin (RatFunc K) (Set.range (fiveRoot t κ))
  have hbase : ∀ a : CommonLiteralField.field K t,
      algebraMap (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ) a ∈ S := by
    have h : Algebra.adjoin (RatFunc K) (Set.range (CommonLiteralField.root K t)) ≤
        S.comap (IsScalarTower.toAlgHom (RatFunc K) (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ)) := by
      apply Algebra.adjoin_le
      rintro _ ⟨i,rfl⟩
      have he : fiveRoot t κ i.castSucc =
          algebraMap (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ)
            (CommonLiteralField.root K t i) := by fin_cases i <;> rfl
      change algebraMap (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ)
        (CommonLiteralField.root K t i) ∈ S
      rw [← he]
      exact Algebra.subset_adjoin ⟨i.castSucc,rfl⟩
    rw [four_root_generates K t] at h
    intro a
    exact h (show a ∈ (⊤ : Subalgebra (RatFunc K) (CommonLiteralField.field K t)) by trivial)
  let SB : Subalgebra (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ) :=
    { S.toSubsemiring with algebraMap_mem' := hbase }
  have hz : fifthRoot t κ ∈ SB := Algebra.subset_adjoin ⟨4,rfl⟩
  have h : Algebra.adjoin (CommonLiteralField.field K t) {fifthRoot t κ} ≤ SB := by
    apply Algebra.adjoin_le
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact hz
  rw [fifth_root_generates K t κ] at h
  apply top_unique
  intro a _
  exact h (show a ∈ (⊤ : Subalgebra (CommonLiteralField.field K t) (CommonGenus17Field.field K t κ)) by trivial)

end FourCorner.ResidueGenerators
#print axioms FourCorner.ResidueGenerators.fiveRoot_sq
#print axioms FourCorner.ResidueGenerators.fiveRoot_generates
