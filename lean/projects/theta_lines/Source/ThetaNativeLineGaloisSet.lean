import ThetaLineSplittingField
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.ThetaLineGaloisAlgebra
open ThetaLinesAbsoluteGalois ThetaLinesDualLines ThetaLinesProjectiveClassification
attribute [local instance] Classical.propDecidable

/-- The literal square-restriction locus over the genuine degree-four field;
this definition does not mention the displayed list. -/
abbrev KLine := {L : ThetaLine K // IsThetaSquareContact L}
/-- The independent native projective-dual square-contact locus in the actual Qbar. -/
abbrev ActualLine := {P : Projectivization Qbar (Module.Dual Qbar (Fin 3 → Qbar)) // dualSquareContact P}

private theorem mapLine_restrict_K (σ : G) (L : ThetaLine K) (x y : K) :
    (mapLine σ.toRingHom L).restrict (σ x) (σ y) = σ (L.restrict x y) := by
  cases L <;> simp [mapLine, ThetaLine.restrict, thetaF, map_add, map_mul, map_sub, map_pow, map_ofNat]

private theorem mapLine_contact_K (σ : G) (L : ThetaLine K) (h : IsThetaSquareContact L) :
    IsThetaSquareContact (mapLine σ.toRingHom L) := by
  obtain ⟨k, a, b, c, hk, he⟩ := h
  refine ⟨σ k, σ a, σ b, σ c, by simpa using σ.injective.ne hk, ?_⟩
  intro x y
  obtain ⟨u, rfl⟩ := σ.surjective x
  obtain ⟨v, rfl⟩ := σ.surjective y
  rw [mapLine_restrict_K, he]
  simp only [map_mul, map_add, map_pow]

instance kLineAction : MulAction G KLine where
  smul σ L := ⟨mapLine σ.toRingHom L.1, mapLine_contact_K σ L.1 L.2⟩
  one_smul L := by
    apply Subtype.ext
    change mapLine (1 : G).toRingHom L.1 = L.1
    cases L.1 <;> rfl
  mul_smul σ τ L := by
    apply Subtype.ext
    change mapLine (σ * τ).toRingHom L.1 = mapLine σ.toRingHom (mapLine τ.toRingHom L.1)
    cases L.1 <;> rfl

instance actualLineAction : MulAction AbsoluteG ActualLine where
  smul σ P := ⟨dualAction σ P.1, (dual_locus_absolute_invariant σ P.1).mpr P.2⟩
  one_smul P := by
    apply Subtype.ext
    change dualAction (1 : AbsoluteG) P.1 = P.1
    obtain ⟨L, hL⟩ := dualLineEquiv.surjective P.1
    rw [← hL, dualAction_line]
    congr 1
    cases L <;> rfl
  mul_smul σ τ P := by
    apply Subtype.ext
    change dualAction (σ * τ) P.1 = dualAction σ (dualAction τ P.1)
    obtain ⟨L, hL⟩ := dualLineEquiv.surjective P.1
    rw [← hL, dualAction_line, dualAction_line, dualAction_line]
    congr 1
    cases L <;> rfl

def toActualLine (L : KLine) : ActualLine := by
  refine ⟨dualLineEquiv (mapLine splittingEmbedding.toRingHom L.1), ?_⟩
  change IsThetaSquareContact (dualLineEquiv.symm (dualLineEquiv _))
  rw [Equiv.symm_apply_apply]
  apply (square_contact_iff_list r s r_sq s_sq _).mpr
  rw [displayedList_embedding]
  exact List.mem_map.mpr ⟨L.1, (theta_all_square_contacts_list L.1).mp L.2, rfl⟩

/-- Actual geometric line descent to the specified finite splitting field. -/
def lineEquiv : KLine ≃ ActualLine := Equiv.ofBijective toActualLine (by
  constructor
  · intro L M h
    apply Subtype.ext
    apply mapLine_injective splittingEmbedding.toRingHom
    apply dualLineEquiv.injective
    exact congrArg Subtype.val h
  · intro P
    have hp := (actual_dual_line_classification P.1).mp P.2
    obtain ⟨L, hL, hLP⟩ := List.mem_map.mp hp
    rw [displayedList_embedding] at hL
    obtain ⟨M, hM, hML⟩ := List.mem_map.mp hL
    subst L
    exact ⟨⟨M, (theta_all_square_contacts_list M).mpr hM⟩, Subtype.ext hLP⟩)

/-- Finite sets here are the independent native loci, classified by the proved list. -/
def membershipEquiv : ActualLine ≃ {P // P ∈ actualDualLines.toFinset} where
  toFun P := ⟨P.1, List.mem_toFinset.mpr ((actual_dual_line_classification P.1).mp P.2)⟩
  invFun P := ⟨P.1, (actual_dual_line_classification P.1).mpr (List.mem_toFinset.mp P.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance actualLineFintype : Fintype ActualLine := Fintype.ofEquiv _ membershipEquiv.symm
instance kLineFintype : Fintype KLine := Fintype.ofEquiv ActualLine lineEquiv.symm

theorem actualLine_card : Fintype.card ActualLine = 28 := by
  rw [Fintype.card_congr membershipEquiv, Fintype.card_coe,
    List.toFinset_card_of_nodup actualDualLines_nodup, actualDualLines_length]
theorem kLine_card : Fintype.card KLine = 28 :=
  (Fintype.card_congr lineEquiv).trans actualLine_card

/-- Compatibility with the ORIGINAL absolute semilinear dual-projective action.
The actual absolute group factors through actual field restriction, not a label action. -/
theorem lineEquiv_absolute (σ : AbsoluteG) (L : KLine) :
    σ • lineEquiv L = lineEquiv (restrictAbsolute σ • L) := by
  apply Subtype.ext
  change dualAction σ (dualLineEquiv (mapLine splittingEmbedding.toRingHom L.1)) =
    dualLineEquiv (mapLine splittingEmbedding.toRingHom (mapLine (restrictAbsolute σ).toRingHom L.1))
  rw [dualAction_line]
  congr 1
  cases L.1 <;> simp [mapLine, ← restrictAbsolute_commutes]
end FourCorner.ThetaLineGaloisAlgebra
