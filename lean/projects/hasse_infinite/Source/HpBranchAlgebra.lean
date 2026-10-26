import HpHenselBranch

namespace FourCorner.HpBranchAlgebra
open HpResidueCharts HpLiteralField HpBranchPlaces
noncomputable section

variable {K : Type*} [Field K] [NeZero (2 : K)]

theorem values_factor (p x : K) (ha : p-1 ≠ 0) (i : Fin 4) :
    values p x i=coefficient K p i*(x-branch K p i) := by
  fin_cases i
  · simp [values,coefficient,branch]
  · simp [values,coefficient,branch]
  · simp [values,coefficient,branch]
  · change (p-1)*x+p+1=(p-1)*(x-(-(p+1)/(p-1)))
    field_simp [ha]
    <;> ring

theorem values_zero_iff (p x : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 4) :
    values p x i=0 ↔ x=branch K p i := by
  rw [values_factor p x ha i,mul_eq_zero]
  simp only [coefficient_ne_zero K p hp ha hb i,false_or,sub_eq_zero]

theorem roots_at_most_one_zero (p x : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (r : Fin 4 → K) (hr : ∀i,r i^2=values p x i) (i : Fin 4) (hi : r i=0) :
    ∀j,j ≠ i → r j ≠ 0 := by
  have hv (j : Fin 4) (hj : r j=0) : x=branch K p j := by
    apply (values_zero_iff p x hp ha hb j).mp
    rw [← hr j,hj]
    norm_num
  intro j hji hj
  exact hji ((branch_injective K p hp ha hb) ((hv j hj).symm.trans (hv i hi)))

theorem map_coefficient {L : Type*} [Field L] [NeZero (2 : L)] (f : K →+* L) (p : K) (i : Fin 4) :
    f (coefficient K p i)=coefficient L (f p) i := by
  fin_cases i <;> simp only [coefficient,map_mul,map_sub,map_add,map_ofNat,map_one]

theorem map_branch {L : Type*} [Field L] [NeZero (2 : L)] (f : K →+* L) (p : K) (i : Fin 4) :
    f (branch K p i)=branch L (f p) i := by
  fin_cases i <;> simp only [branch,map_div₀,map_neg,map_sub,map_add,map_zero,map_one]

theorem pivot_parameter (p : ℚ) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (i : Fin 4) {q : ℕ} [Fact q.Prime] (u : ℚ_[q]) :
    u^2=values (p : ℚ_[q])
      (((branch ℚ p i : ℚ) : ℚ_[q])+((coefficient ℚ p i)⁻¹ : ℚ)*u^2) i := by
  have hpa : (p : ℚ_[q])-1 ≠ 0 := by exact_mod_cast ha
  have hc : ((coefficient ℚ p i : ℚ) : ℚ_[q]) ≠ 0 := by
    exact_mod_cast coefficient_ne_zero ℚ p hp ha hb i
  have hm : ((branch ℚ p i : ℚ) : ℚ_[q])=branch ℚ_[q] (p : ℚ_[q]) i := by
    simpa using map_branch (Rat.castHom ℚ_[q]) p i
  have hmc : ((coefficient ℚ p i : ℚ) : ℚ_[q])=coefficient ℚ_[q] (p : ℚ_[q]) i := by
    simpa using map_coefficient (Rat.castHom ℚ_[q]) p i
  rw [values_factor _ _ hpa,← hm,← hmc]
  change u^2=((coefficient ℚ p i : ℚ) : ℚ_[q])*
    ((((branch ℚ p i : ℚ) : ℚ_[q])+((coefficient ℚ p i)⁻¹ : ℚ)*u^2)-((branch ℚ p i : ℚ) : ℚ_[q]))
  push_cast
  field_simp [hc]
  ring

#print axioms roots_at_most_one_zero
#print axioms pivot_parameter
end
end FourCorner.HpBranchAlgebra
