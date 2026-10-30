import Genus17Model
import FiveSquareDegree

noncomputable section
namespace FourCorner.Genus17Geometry
open IntermediateField
variable {K : Type*} [Field K] [CharZero K]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

def fiveRoot (t κ : K) : Fin 5 → field t κ
  | 0 => orderedRoot t κ 0
  | 1 => orderedRoot t κ 1
  | 2 => orderedRoot t κ 2
  | 3 => orderedRoot t κ 3
  | 4 => fifthRoot t κ

theorem fiveRoot_sq (t κ : K) (i : Fin 5) : fiveRoot t κ i ^ 2 =
    algebraMap (RatFunc K) (field t κ) (CommonFiveIndependence.value t κ i) := by
  fin_cases i
  all_goals simp only [fiveRoot,orderedRoot,CommonFiveIndependence.value]
  all_goals first
    | rw [← map_pow,CommonLiteralField.root_sq]
      rfl
    | exact fifthRoot_sq t κ

/-- All five literal ordered roots generate the actual tower field. -/
theorem fiveRoot_generates (t κ : K) :
    Algebra.adjoin (RatFunc K) (Set.range (fiveRoot t κ)) = ⊤ := by
  let S := Algebra.adjoin (RatFunc K) (Set.range (fiveRoot t κ))
  have hbase : ∀ a : baseField t, algebraMap (baseField t) (field t κ) a ∈ S := by
    have h : Algebra.adjoin (RatFunc K)
        {CommonLiteralField.root K t 0,CommonLiteralField.root K t 1,
          CommonLiteralField.root K t 2,CommonLiteralField.root K t 3} ≤
        S.comap (IsScalarTower.toAlgHom (RatFunc K) (baseField t) (field t κ)) := by
      apply Algebra.adjoin_le
      intro a ha
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
      rcases ha with rfl|rfl|rfl|rfl
      · exact Algebra.subset_adjoin ⟨0,rfl⟩
      · exact Algebra.subset_adjoin ⟨1,rfl⟩
      · exact Algebra.subset_adjoin ⟨2,rfl⟩
      · exact Algebra.subset_adjoin ⟨3,rfl⟩
    rw [CommonLiteralField.root_generates] at h
    intro a
    exact h (show a ∈ (⊤ : Subalgebra (RatFunc K) (baseField t)) by trivial)
  let SB : Subalgebra (baseField t) (field t κ) :=
    { S.toSubsemiring with algebraMap_mem' := hbase }
  have hz : fifthRoot t κ ∈ SB := Algebra.subset_adjoin ⟨4,rfl⟩
  have h : Algebra.adjoin (baseField t) {fifthRoot t κ} ≤ SB := by
    apply Algebra.adjoin_le
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact hz
  rw [CommonGenus17Unramified.Extension.root_generates K t κ] at h
  apply top_unique
  intro a _
  exact h (show a ∈ (⊤ : Subalgebra (baseField t) (field t κ)) by trivial)

theorem degree_thirtyTwo (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    Module.finrank (RatFunc K) (field t κ) = 32 := by
  letI : FiniteDimensional (RatFunc K) (baseField t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  rw [← Module.finrank_mul_finrank (RatFunc K) (baseField t) (field t κ),
    CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm,degree_two t κ h0 h1 hm hκ]
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.fiveRoot_sq
#print axioms FourCorner.Genus17Geometry.fiveRoot_generates
#print axioms FourCorner.Genus17Geometry.degree_thirtyTwo
