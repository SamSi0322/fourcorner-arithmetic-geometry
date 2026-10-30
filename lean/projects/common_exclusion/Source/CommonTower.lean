import geometry.MultiquadraticTower
import CommonFourDegree

noncomputable section
set_option maxHeartbeats 800000
namespace FourCorner.CommonTower
open IntermediateField
variable (F L : Type*) [Field F] [Field L] [Algebra F L]

abbrev first (r : L) := IntermediateField.adjoin F {r}
abbrev second (r s : L) := IntermediateField.adjoin F {r,s}
abbrev third (r s u : L) := IntermediateField.adjoin F {r,s,u}

theorem first_le_second (r s : L) : first F L r ≤ second F L r s := by
  apply IntermediateField.adjoin.mono
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  simp [hx]

theorem second_le_third (r s u : L) : second F L r s ≤ third F L r s u := by
  apply IntermediateField.adjoin.mono
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢
  tauto

instance algebra12 (r s : L) : Algebra (first F L r) (second F L r s) :=
  (IntermediateField.inclusion (first_le_second F L r s)).toRingHom.toAlgebra
instance algebra23 (r s u : L) : Algebra (second F L r s) (third F L r s u) :=
  (IntermediateField.inclusion (second_le_third F L r s u)).toRingHom.toAlgebra
instance algebra13 (r s u : L) : Algebra (first F L r) (third F L r s u) :=
  (IntermediateField.inclusion ((first_le_second F L r s).trans (second_le_third F L r s u))).toRingHom.toAlgebra
instance towerF12 (r s : L) : IsScalarTower F (first F L r) (second F L r s) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance towerF23 (r s u : L) : IsScalarTower F (second F L r s) (third F L r s u) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance towerF13 (r s u : L) : IsScalarTower F (first F L r) (third F L r s u) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance tower123 (r s u : L) : IsScalarTower (first F L r) (second F L r s) (third F L r s u) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance tower12L (r s : L) : IsScalarTower (first F L r) (second F L r s) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance tower23L (r s u : L) : IsScalarTower (second F L r s) (third F L r s u) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance tower13L (r s u : L) : IsScalarTower (first F L r) (third F L r s u) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable [FiniteDimensional F L]

def r1 (r : L) : first F L r := ⟨r,subset_adjoin F _ (by simp)⟩
def r2 (r s : L) : second F L r s := ⟨s,subset_adjoin F _ (by simp)⟩
def r3 (r s u : L) : third F L r s u := ⟨u,subset_adjoin F _ (by simp)⟩

theorem gen1 (r : L) : Algebra.adjoin F {r1 F L r} = ⊤ := by
  have hgen : IntermediateField.adjoin F {r1 F L r} = ⊤ := by
    apply IntermediateField.lift_injective (first F L r)
    rw [IntermediateField.lift_adjoin_simple,IntermediateField.lift_top]
    rfl
  apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic _).mp hgen
  simpa using (IsIntegral.of_finite F (r1 F L r)).isAlgebraic

theorem gen2 (r s : L) : Algebra.adjoin (first F L r) {r2 F L r s} = ⊤ := by
  apply Multiquadratic.Tower.Auxiliary.generator_top
    (first F L r) (second F L r s) (first_le_second F L r s) s
    (subset_adjoin F _ (by simp))
  · have h := IntermediateField.adjoin_adjoin_left (F:=F) (S:={r}) ({s}:Set L)
    rw [Set.singleton_union] at h
    exact h.symm
  · exact (IsIntegral.of_finite F s).tower_top.isAlgebraic

theorem gen3 (r s u : L) : Algebra.adjoin (second F L r s) {r3 F L r s u} = ⊤ := by
  apply Multiquadratic.Tower.Auxiliary.generator_top
    (second F L r s) (third F L r s u) (second_le_third F L r s u) u
    (subset_adjoin F _ (by simp))
  · have h := IntermediateField.adjoin_adjoin_left (F:=F) (S:={r,s}) ({u}:Set L)
    have he : ({r,s}:Set L) ∪ {u} = {r,s,u} := by ext x; simp; tauto
    rw [he] at h
    exact h.symm
  · exact (IsIntegral.of_finite F u).tower_top.isAlgebraic

/-- The final fourth generator, inside the actual ambient field. -/
theorem gen4 (r s u v : L) (hgen : Algebra.adjoin F {r,s,u,v} = ⊤) :
    Algebra.adjoin (third F L r s u) {v} = ⊤ := by
  let S := Algebra.adjoin (third F L r s u) {v}
  have hs : Algebra.adjoin F {r,s,u,v} ≤ S.restrictScalars F := by
    apply Algebra.adjoin_le
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]
      exact S.algebraMap_mem (⟨r,subset_adjoin F _ (by simp)⟩ : third F L r s u)
    · rw [hx]
      exact S.algebraMap_mem (⟨s,subset_adjoin F _ (by simp)⟩ : third F L r s u)
    · rw [hx]
      exact S.algebraMap_mem (⟨u,subset_adjoin F _ (by simp)⟩ : third F L r s u)
    · rw [hx]
      exact Algebra.subset_adjoin (by simp)
  rw [hgen] at hs
  apply top_unique
  exact hs

/-- A primitive quadratic root gives a genuine degree at most two. -/
theorem finrank_le_two {a : F} {r : L} (hr : r^2 = algebraMap F L a)
    (hgen : Algebra.adjoin F {r} = ⊤) : Module.finrank F L ≤ 2 := by
  have hi : IsIntegral F r := by
    refine ⟨Polynomial.X^2-Polynomial.C a, Polynomial.monic_X_pow_sub_C a (by decide), ?_⟩
    simp [hr]
  have hd : (minpoly F r).natDegree ≤ 2 := by
    simpa using Polynomial.natDegree_le_natDegree
      (minpoly.min F r (Polynomial.monic_X_pow_sub_C a (by norm_num)) (by simp [hr]))
  have hJ : IntermediateField.adjoin F {r} = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic (by simpa using hi.isAlgebraic)).mpr hgen
  have hf := IntermediateField.adjoin.finrank hi
  rw [hJ, IntermediateField.finrank_top'] at hf
  exact hf.le.trans hd

#print axioms finrank_le_two
#print axioms gen4
end FourCorner.CommonTower
