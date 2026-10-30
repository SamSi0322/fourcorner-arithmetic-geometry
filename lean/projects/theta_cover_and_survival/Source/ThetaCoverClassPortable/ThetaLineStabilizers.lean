import ThetaCoverClassPortable.ThetaLineFixedFields
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
noncomputable section
namespace FourCorner.ThetaLineGaloisAlgebra
attribute [local instance] Classical.propDecidable

theorem fixedAt_mem_iff (L : KLine) (z : K) :
    z ∈ fixedAt L ↔
      (thetaFlipTwo • L = L → thetaFlipTwo z = z) ∧
      (thetaFlipFiftyone • L = L → thetaFlipFiftyone z = z) ∧
      (thetaFlipTwo.trans thetaFlipFiftyone • L = L →
        thetaFlipTwo.trans thetaFlipFiftyone z = z) := by
  constructor
  · intro h
    exact ⟨h _, h _, h _⟩
  · rintro ⟨hR, hS, hRS⟩ σ hσ
    rcases theta_aut_four_cases σ with h | h | h | h
    · subst σ; rfl
    · subst σ; exact hR hσ
    · subst σ; exact hS hσ
    · subst σ; exact hRS hσ

@[simp] theorem two_fixes_representative (i : Fin 17) :
    (thetaFlipTwo • representative i = representative i) ↔
      twoIndex (representativeIndex i) = representativeIndex i := by
  rw [representative, two_action_index]
  exact lineIndexEquiv.injective.eq_iff
@[simp] theorem fiftyone_fixes_representative (i : Fin 17) :
    (thetaFlipFiftyone • representative i = representative i) ↔
      fiftyoneIndex (representativeIndex i) = representativeIndex i := by
  rw [representative, fiftyone_action_index]
  exact lineIndexEquiv.injective.eq_iff
@[simp] theorem both_fixes_representative (i : Fin 17) :
    (thetaFlipTwo.trans thetaFlipFiftyone • representative i = representative i) ↔
      fiftyoneIndex (twoIndex (representativeIndex i)) = representativeIndex i := by
  change ((thetaFlipFiftyone * thetaFlipTwo) • lineIndexEquiv (representativeIndex i) = _) ↔ _
  rw [mul_smul, two_action_index, fiftyone_action_index]
  exact lineIndexEquiv.injective.eq_iff

/-- Computed stabilizer-fixed VALUE algebras, after the true native orbit classification. -/
def orbitValueAlgebra (i : Fin 17) : Subalgebra ℚ K :=
  if i.val < 8 then fixedRational
  else if i.val < 12 then fixedTwo
  else if i.val < 16 then fixedFiftyone
  else ⊤

theorem fixedAt_eq_orbitValueAlgebra (i : Fin 17) :
    fixedAt (representative i) = orbitValueAlgebra i := by
  ext z
  rw [fixedAt_mem_iff]
  have hprod : thetaFlipTwo z = z → thetaFlipFiftyone z = z →
      thetaFlipTwo.trans thetaFlipFiftyone z = z := by
    intro hR hS
    simp only [AlgEquiv.trans_apply, hR, hS]
  fin_cases i <;> norm_num [two_fixes_representative, fiftyone_fixes_representative,
    both_fixes_representative, representativeIndex, twoIndex, fiftyoneIndex,
    orbitValueAlgebra, fixedRational, fixedTwo, fixedFiftyone, fixedBy]
  all_goals tauto

def orbitValueEquiv (i : Fin 17) : fixedAt (representative i) ≃ₐ[ℚ] orbitValueAlgebra i :=
  Subalgebra.equivOfEq _ _ (fixedAt_eq_orbitValueAlgebra i)

def associatedOrbitValuesEquiv : Associated ≃ₐ[ℚ] (∀ i : Fin 17, orbitValueAlgebra i) :=
  orbitEvaluationEquiv.trans (AlgEquiv.piCongrRight orbitValueEquiv)
end FourCorner.ThetaLineGaloisAlgebra
