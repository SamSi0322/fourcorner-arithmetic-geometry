import ThetaLinesProjectiveClassification

namespace FourCorner.ThetaLinesGaloisAction
open ThetaLinesProjectiveLines ThetaLinesAbsoluteGalois ThetaLinesProjectiveClassification
noncomputable section
attribute [local instance] Classical.propDecidable

 theorem mapLine_restrict (σ : Qbar ≃ₐ[ℚ] Qbar) (L : ThetaLine Qbar) (x y : Qbar) :
    (mapLine σ.toRingHom L).restrict (σ x) (σ y)=σ (L.restrict x y) := by
  cases L <;> simp [mapLine,ThetaLine.restrict,thetaF,map_add,map_mul,map_sub,map_pow,map_ofNat]

 theorem mapLine_square_contact (σ : Qbar ≃ₐ[ℚ] Qbar) (L : ThetaLine Qbar)
    (h : IsThetaSquareContact L) : IsThetaSquareContact (mapLine σ.toRingHom L) := by
  obtain ⟨k,a,b,c,hk,he⟩ := h
  refine ⟨σ k,σ a,σ b,σ c,by simpa using σ.injective.ne hk,?_⟩
  intro x y
  obtain ⟨u,rfl⟩ := σ.surjective x
  obtain ⟨v,rfl⟩ := σ.surjective y
  rw [mapLine_restrict,he]
  simp only [map_mul,map_add,map_pow]

 theorem mapLine_square_contact_iff (σ : Qbar ≃ₐ[ℚ] Qbar) (L : ThetaLine Qbar) :
    IsThetaSquareContact (mapLine σ.toRingHom L) ↔ IsThetaSquareContact L := by
  constructor
  · intro h
    have hh := mapLine_square_contact σ.symm _ h
    cases L <;> simpa [mapLine] using hh
  · exact mapLine_square_contact σ L

 @[simp] theorem coordinateMap_apply (σ : Qbar ≃ₐ[ℚ] Qbar) (v : Fin 3 → Qbar) (i : Fin 3) : coordinateMap σ v i=σ (v i) := rfl

 theorem projectiveAction_geometricLine (σ : Qbar ≃ₐ[ℚ] Qbar) (L : ThetaLine Qbar) :
    projectiveAction σ (geometricLine L)=geometricLine (mapLine σ.toRingHom L) := by
  change Projectivization.map _ _ (Projectivization.mk _ _ _)=_
  rw [Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff' Qbar _ _ _ _).mpr
  refine ⟨1,?_⟩
  cases L <;> ext i <;> fin_cases i
  all_goals change _=σ _
  all_goals simp [coefficients,mapLine]

/-- The ACTUAL absolute Galois semilinear action preserves the ACTUAL
native projective square-contact locus of the original quartic. -/
 theorem absolute_preserves_native_locus (σ : Qbar ≃ₐ[ℚ] Qbar) (P : Projectivization Qbar (Fin 3 → Qbar)) :
    nativeSquareContact (projectiveAction σ P) ↔ nativeSquareContact P := by
  obtain ⟨L,rfl⟩ := geometricLine_surjective P
  rw [projectiveAction_geometricLine]
  have hL (M : ThetaLine Qbar) : lineEquiv.symm (geometricLine M)=M := lineEquiv.symm_apply_apply M
  simp only [nativeSquareContact,hL]
  exact mapLine_square_contact_iff σ L

 theorem displayedList_map (σ : Qbar ≃ₐ[ℚ] Qbar) :
    (displayedList r s).map (mapLine σ.toRingHom)=displayedList (σ r) (σ s) := by
  simp [displayedList,mapLine,map_ofNat]

/-- On the actual twenty-eight geometric line equations, every absolute
Galois element acts by its actual signs on r and s. -/
 theorem actual_displayed_action (σ : Qbar ≃ₐ[ℚ] Qbar) :
    actualDisplayedLines.map (projectiveAction σ)=
      (displayedList (σ r) (σ s)).map geometricLine := by
  rw [← displayedList_map]
  simp only [actualDisplayedLines,List.map_map]
  congr 1
  funext L
  exact projectiveAction_geometricLine σ L

#print axioms absolute_preserves_native_locus
#print axioms actual_displayed_action
#print axioms FourCorner.ThetaLinesAbsoluteGalois.absolute_independent_signs
#print axioms FourCorner.ThetaLinesAbsoluteGalois.absolute_radical_signs
end
end FourCorner.ThetaLinesGaloisAction
