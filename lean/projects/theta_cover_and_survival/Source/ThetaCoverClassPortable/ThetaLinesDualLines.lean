import ThetaCoverClassPortable.ThetaLinesGaloisAction

namespace FourCorner.ThetaLinesDualLines
open ThetaLinesProjectiveLines ThetaLinesProjectiveClassification ThetaLinesAbsoluteGalois
noncomputable section
attribute [local instance] Classical.propDecidable

 def projectiveEquiv {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) : Projectivization K V ≃ Projectivization K W where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      simp only [Projectivization.map_mk]
      congr 1
      exact e.symm_apply_apply v
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      simp only [Projectivization.map_mk]
      congr 1
      exact e.apply_symm_apply v

/-- The proved correspondence is with native projectivized actual linear
forms (the dual plane), not merely a coefficient-tuple label type. -/
def dualLineEquiv {K : Type*} [Field K] :
    ThetaLine K ≃ Projectivization K (Module.Dual K (Fin 3 → K)) :=
  lineEquiv.trans (projectiveEquiv (dotProductEquiv K (Fin 3)))

theorem dualLineEquiv_apply {K : Type*} [Field K] (L : ThetaLine K) : dualLineEquiv L=dualLine L := rfl

def actualDualLines : List (Projectivization Qbar (Module.Dual Qbar (Fin 3 → Qbar))) :=
  (displayedList r s).map dualLineEquiv

theorem actualDualLines_nodup : actualDualLines.Nodup := displayedList_nodup.map dualLineEquiv.injective

theorem actualDualLines_length : actualDualLines.length=28 := rfl

/-- Literal quartic square-restriction condition, independent of any list,
on an ACTUAL projectivized linear form of the original plane. -/
def dualSquareContact (P : Projectivization Qbar (Module.Dual Qbar (Fin 3 → Qbar))) : Prop :=
  IsThetaSquareContact (dualLineEquiv.symm P)

theorem actual_dual_line_classification (P : Projectivization Qbar (Module.Dual Qbar (Fin 3 → Qbar))) :
    dualSquareContact P ↔ P∈actualDualLines := by
  constructor
  · intro h
    exact List.mem_map.mpr ⟨dualLineEquiv.symm P,
      (square_contact_iff_list r s r_sq s_sq _).mp h,dualLineEquiv.apply_symm_apply P⟩
  · intro h
    obtain ⟨L,hL,rfl⟩ := List.mem_map.mp h
    change IsThetaSquareContact (dualLineEquiv.symm (dualLineEquiv L))
    rw [Equiv.symm_apply_apply]
    exact (square_contact_iff_list r s r_sq s_sq _).mpr hL

/-- Absolute semilinear action transported through the ACTUAL basis
isomorphism between coefficient vectors and linear forms. -/
def dualAction (σ : Qbar ≃ₐ[ℚ] Qbar)
    (P : Projectivization Qbar (Module.Dual Qbar (Fin 3 → Qbar))) :=
  projectiveEquiv (dotProductEquiv Qbar (Fin 3))
    (projectiveAction σ ((projectiveEquiv (dotProductEquiv Qbar (Fin 3))).symm P))

theorem dualAction_line (σ : Qbar ≃ₐ[ℚ] Qbar) (L : ThetaLine Qbar) :
    dualAction σ (dualLineEquiv L)=dualLineEquiv (mapLine σ.toRingHom L) := by
  change projectiveEquiv (dotProductEquiv Qbar (Fin 3))
    (projectiveAction σ ((projectiveEquiv (dotProductEquiv Qbar (Fin 3))).symm
      ((projectiveEquiv (dotProductEquiv Qbar (Fin 3))) (geometricLine L))))=_
  rw [Equiv.symm_apply_apply,ThetaLinesGaloisAction.projectiveAction_geometricLine]
  rfl

theorem actual_dual_absolute_action (σ : Qbar ≃ₐ[ℚ] Qbar) :
    actualDualLines.map (dualAction σ)=(displayedList (σ r) (σ s)).map dualLineEquiv := by
  rw [← ThetaLinesGaloisAction.displayedList_map]
  simp only [actualDualLines,List.map_map]
  congr 1
  funext L
  exact dualAction_line σ L

theorem dual_locus_absolute_invariant (σ : Qbar ≃ₐ[ℚ] Qbar)
    (P : Projectivization Qbar (Module.Dual Qbar (Fin 3 → Qbar))) :
    dualSquareContact (dualAction σ P) ↔ dualSquareContact P := by
  obtain ⟨L,rfl⟩ := dualLineEquiv.surjective P
  rw [dualAction_line]
  simp only [dualSquareContact,Equiv.symm_apply_apply]
  exact ThetaLinesGaloisAction.mapLine_square_contact_iff σ L

#print axioms actual_dual_absolute_action
#print axioms dual_locus_absolute_invariant
#print axioms dualLineEquiv
#print axioms actualDualLines_nodup
#print axioms actualDualLines_length
#print axioms actual_dual_line_classification
end
end FourCorner.ThetaLinesDualLines
