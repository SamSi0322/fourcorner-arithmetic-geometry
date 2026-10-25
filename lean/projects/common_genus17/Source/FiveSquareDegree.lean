import CommonFifthDegree

noncomputable section
namespace FourCorner.FiveSquareDegree
open IntermediateField
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Five genuinely independent squareclasses generate a degree-32 field;
the last quadratic step is derived from the four-root square criterion. -/
theorem finrank_eq_thirtyTwo (q : Fin 5 → F) (r : Fin 5 → L)
    (hr : ∀ i, r i ^ 2 = algebraMap F L (q i)) (h2 : (2:F) ≠ 0)
    (hind : ∀ s : Finset (Fin 5), s.Nonempty → ¬ IsSquare (∏ i ∈ s,q i)) :
    Module.finrank F (IntermediateField.adjoin F (Set.range r)) = 32 := by
  let r4 : Fin 4 → L := fun i => r i.castSucc
  let J := IntermediateField.adjoin F {r4 0,r4 1,r4 2,r4 3}
  have hind4 : ∀ s : Finset (Fin 4), s.Nonempty → ¬ IsSquare (∏ i ∈ s,q i.castSucc) := by
    intro s hs
    have h := hind (s.map (Fin.castLEEmb (by decide : 4 ≤ 5))) (Finset.map_nonempty.mpr hs)
    have he : (∏ i ∈ s.map (Fin.castLEEmb (by decide : 4 ≤ 5)),q i) = ∏ i ∈ s,q i.castSucc := by
      rw [Finset.prod_map]
      apply Finset.prod_congr rfl
      intro i _
      fin_cases i <;> rfl
    rwa [he] at h
  have hJ : Module.finrank F J = 16 :=
    CommonFourDegree.finrank_four_eq_sixteen_of_products (fun i => q i.castSucc) r4
      (fun i => hr i.castSucc) h2 hind4
  letI : FiniteDimensional F J := FiniteDimensional.of_finrank_pos (by rw [hJ]; norm_num)
  have hns : ¬ IsSquare (algebraMap F J (q 4)) :=
    CommonFifthDegree.fifth_nonsquare_of_products q r4 (fun i => hr i.castSucc) h2 hind
  let T := IntermediateField.adjoin J {r 4}
  have hsq : r 4 ^ 2 = algebraMap J L (algebraMap F J (q 4)) :=
    (hr 4).trans (IsScalarTower.algebraMap_apply F J L (q 4))
  have hT : Module.finrank J T = 2 := by
    apply Multiquadratic.finrank_adjoin_square_root _ hsq
    intro x hx
    exact hns ⟨x,by simpa only [sq] using hx.symm⟩
  letI : FiniteDimensional J T := FiniteDimensional.of_finrank_pos (by rw [hT]; norm_num)
  have hdeg : Module.finrank F T = 32 := by
    rw [← Module.finrank_mul_finrank F J T,hJ,hT]
  have he : T.restrictScalars F = IntermediateField.adjoin F (Set.range r) := by
    have h := IntermediateField.adjoin_adjoin_left (F := F) (S := {r4 0,r4 1,r4 2,r4 3}) ({r 4} : Set L)
    change (IntermediateField.adjoin J {r 4}).restrictScalars F = _
    rw [h]
    congr 1
    ext x
    simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_range]
    constructor
    · rintro (h|h)
      · rcases h with h|h|h|h
        · exact ⟨0,h.symm⟩
        · exact ⟨1,h.symm⟩
        · exact ⟨2,h.symm⟩
        · exact ⟨3,h.symm⟩
      · exact ⟨4,h.symm⟩
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp [r4]
  exact ((IntermediateField.equivOfEq he).toLinearEquiv.finrank_eq).symm.trans hdeg
end FourCorner.FiveSquareDegree
#print axioms FourCorner.FiveSquareDegree.finrank_eq_thirtyTwo
