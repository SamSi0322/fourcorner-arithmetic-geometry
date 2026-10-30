import ThetaCoverClassPortable.ThetaAssociatedLineAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
noncomputable section
namespace FourCorner.ThetaLineGaloisAlgebra
open ThetaLinesProjectiveClassification
attribute [local instance] Classical.propDecidable

private def listMembershipEquiv : {L // L ∈ thetaTwentyEightLines} ≃ KLine where
  toFun L := ⟨L.1, (theta_all_square_contacts_list L.1).mpr L.2⟩
  invFun L := ⟨L.1, (theta_all_square_contacts_list L.1).mp L.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A proved enumeration of the independent actual K-line locus. -/
def lineIndexEquiv : Fin 28 ≃ KLine :=
  (List.Nodup.getEquiv thetaTwentyEightLines theta_twenty_eight_distinct).trans listMembershipEquiv

/-- These permutations are only a computed description of the actual field actions. -/
def twoIndex : Fin 28 → Fin 28 :=
  ![2,3,0,1,6,7,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,26,27,24,25]
def fiftyoneIndex : Fin 28 → Fin 28 :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,19,18,17,16,23,22,21,20,27,26,25,24]

theorem two_action_index (i : Fin 28) :
    thetaFlipTwo • lineIndexEquiv i = lineIndexEquiv (twoIndex i) := by
  apply Subtype.ext
  change mapLine thetaFlipTwo.toRingHom (thetaTwentyEightLines.get i) =
    thetaTwentyEightLines.get (twoIndex i)
  fin_cases i <;> simp [thetaTwentyEightLines, twoIndex, mapLine, map_ofNat]

theorem fiftyone_action_index (i : Fin 28) :
    thetaFlipFiftyone • lineIndexEquiv i = lineIndexEquiv (fiftyoneIndex i) := by
  apply Subtype.ext
  change mapLine thetaFlipFiftyone.toRingHom (thetaTwentyEightLines.get i) =
    thetaTwentyEightLines.get (fiftyoneIndex i)
  fin_cases i <;> simp [thetaTwentyEightLines, fiftyoneIndex, mapLine, map_ofNat]
  all_goals congr 1 <;> ring

/-- Eight rational orbits, four sqrt(2)-orbits, four sqrt(51)-orbits and the regular orbit. -/
def orbitIndex : Fin 28 → Fin 17 :=
  ![8,9,8,9,10,11,10,11,0,1,2,3,4,5,6,7,12,13,13,12,14,15,15,14,16,16,16,16]
def representativeIndex : Fin 17 → Fin 28 :=
  ![8,9,10,11,12,13,14,15,0,1,4,5,16,17,20,21,24]
def representative (i : Fin 17) : KLine := lineIndexEquiv (representativeIndex i)
def orbitOf (L : KLine) : Fin 17 := orbitIndex (lineIndexEquiv.symm L)

theorem orbitIndex_two : ∀ i, orbitIndex (twoIndex i) = orbitIndex i := by decide
theorem orbitIndex_fiftyone : ∀ i, orbitIndex (fiftyoneIndex i) = orbitIndex i := by decide
theorem orbitIndex_representative : ∀ i, orbitIndex (representativeIndex i) = i := by decide

theorem orbitOf_representative (i : Fin 17) : orbitOf (representative i) = i := by
  simp only [orbitOf, representative, Equiv.symm_apply_apply, orbitIndex_representative]

theorem orbitOf_action (σ : G) (L : KLine) : orbitOf (σ • L) = orbitOf L := by
  obtain ⟨i, rfl⟩ := lineIndexEquiv.surjective L
  rcases theta_aut_four_cases σ with h | h | h | h
  · subst σ
    change orbitOf ((1 : G) • lineIndexEquiv i) = _
    rw [one_smul]
  · subst σ
    rw [two_action_index]
    simp only [orbitOf, Equiv.symm_apply_apply, orbitIndex_two]
  · subst σ
    rw [fiftyone_action_index]
    simp only [orbitOf, Equiv.symm_apply_apply, orbitIndex_fiftyone]
  · subst σ
    change orbitOf ((thetaFlipFiftyone * thetaFlipTwo) • lineIndexEquiv i) = _
    rw [mul_smul, two_action_index, fiftyone_action_index]
    simp only [orbitOf, Equiv.symm_apply_apply, orbitIndex_two, orbitIndex_fiftyone]

private def twoBit : Fin 28 → Bool :=
  ![false,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,
    false,false,false,false,false,false,false,false,false,true,true,false]
private def fiftyoneBit : Fin 28 → Bool :=
  ![false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,
    false,false,true,true,false,false,true,true,false,true,false,true]

def orbitMover (L : KLine) : G :=
  signAut (twoBit (lineIndexEquiv.symm L)) (fiftyoneBit (lineIndexEquiv.symm L))

theorem orbitMover_spec (L : KLine) : orbitMover L • representative (orbitOf L) = L := by
  obtain ⟨i, rfl⟩ := lineIndexEquiv.surjective L
  simp only [orbitMover, orbitOf, representative, Equiv.symm_apply_apply]
  fin_cases i
  all_goals simp only [twoBit, fiftyoneBit, orbitIndex, representativeIndex, signAut,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
    Fin.isValue, Bool.false_eq_true, ↓reduceIte]
  all_goals first
    | rfl
    | (exact two_action_index _)
    | (exact fiftyone_action_index _)
    | (change (thetaFlipFiftyone * thetaFlipTwo) • _ = _
       rw [mul_smul, two_action_index, fiftyone_action_index]
       rfl)
end FourCorner.ThetaLineGaloisAlgebra
