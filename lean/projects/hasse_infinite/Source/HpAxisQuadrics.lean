import HpDiagonalNet

namespace FourCorner.HpAxisQuadrics
open HpQuadraticRelations HpDiagonalNet
noncomputable section
variable (K : Type*) [Field K] [CharZero K]
attribute [local instance] Classical.propDecidable

def determinant (p : K) (i j : Fin 5) : K := slope K p i*intercept K p j-slope K p j*intercept K p i

def determinantTable (p : K) : Fin 5 → Fin 5 → K :=
  ![![0,-2*p*(p-1),2*p*(p+1),p*(p+1),p],
    ![2*p*(p-1),0,8*(p-1)*(p+1),4*p*(p-1),2*(p-1)],
    ![-2*p*(p+1),-8*(p-1)*(p+1),0,4*(p+1),2*(p+1)],
    ![-p*(p+1),-4*p*(p-1),-4*(p+1),0,p-1],
    ![-p,-2*(p-1),-2*(p+1),-(p-1),0]]

theorem determinant_eq_table (p : K) (i j : Fin 5) : determinant K p i j=determinantTable K p i j := by
  fin_cases i <;> fin_cases j <;> simp [determinant,determinantTable,slope,intercept] <;> ring

theorem determinant_ne_zero (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (i j : Fin 5) (hij : i ≠ j) : determinant K p i j ≠ 0 := by
  have han : 1-p ≠ 0 := by intro h;apply ha;linear_combination -h
  rw [determinant_eq_table]
  fin_cases i <;> fin_cases j <;> simp [determinantTable,hp,ha,hb,han,mul_ne_zero] at *

private theorem linear_ne (a b t : K) (hb : b ≠ 0) (ht : t ≠ -a/b) : a+t*b ≠ 0 := by
  intro h
  apply ht
  apply (eq_div_iff hb).mpr
  exact eq_neg_of_add_eq_zero_right h

/-- Four pairwise independent columns in a two-dimensional space have a
relation in which all four coefficients are nonzero. -/
theorem four_nonzero_relation (u v : Fin 4 → K)
    (hd : ∀i j : Fin 4,i ≠ j → u i*v j-u j*v i ≠ 0) :
    ∃d : Fin 4 → K,(∀i,d i ≠ 0) ∧ (∑i,d i*u i)=0 ∧ (∑i,d i*v i)=0 := by
  letI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  let Δ (i j : Fin 4) := u i*v j-u j*v i
  obtain ⟨t,ht⟩ := ({0,-Δ 1 2/Δ 1 3,-Δ 2 0/Δ 3 0} : Finset K).exists_notMem
  have ht0 : t ≠ 0 := by intro h;exact ht (by simp [h])
  have ht1 : t ≠ -Δ 1 2/Δ 1 3 := by intro h;exact ht (by simp [h])
  have ht2 : t ≠ -Δ 2 0/Δ 3 0 := by intro h;exact ht (by simp [h])
  let d : Fin 4 → K := ![Δ 1 2+t*Δ 1 3,Δ 2 0+t*Δ 3 0,Δ 0 1,t*Δ 0 1]
  refine ⟨d,?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact linear_ne K _ _ _ (hd 1 3 (by decide)) ht1
    · exact linear_ne K _ _ _ (hd 3 0 (by decide)) ht2
    · exact hd 0 1 (by decide)
    · exact mul_ne_zero ht0 (hd 0 1 (by decide))
  · simp [d,Fin.sum_univ_succ,Δ]
    ring
  · simp [d,Fin.sum_univ_succ,Δ]
    ring

/-- Each of the five coordinate axes is realized as the unique zero
coefficient of an actual diagonal quadric relation. -/
theorem exists_unique_zero_coefficient (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (i : Fin 5) :
    ∃d : Fin 5 → K,d∈net K p ∧ d i=0 ∧ ∀j,j ≠ i → d j ≠ 0 := by
  let u : Fin 4 → K := fun j => slope K p (i.succAbove j)
  let v : Fin 4 → K := fun j => intercept K p (i.succAbove j)
  have hd (j k : Fin 4) (hjk : j ≠ k) : u j*v k-u k*v j ≠ 0 := by
    exact determinant_ne_zero K p hp ha hb _ _ (fun h => hjk (Fin.succAbove_right_injective h))
  obtain ⟨d,hn,hu,hv⟩ := four_nonzero_relation K u v hd
  refine ⟨i.insertNth 0 d,?_,Fin.insertNth_apply_same _ _ _,?_⟩
  · rw [mem_net]
    constructor
    · rw [slopeSum,Fin.sum_univ_succAbove _ i]
      simpa only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,zero_mul,zero_add] using hu
    · rw [interceptSum,Fin.sum_univ_succAbove _ i]
      simpa only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,zero_mul,zero_add] using hv
  · intro j hj
    obtain ⟨k,rfl⟩ := (Fin.exists_succAbove_eq hj)
    simpa only [Fin.insertNth_apply_succAbove] using hn k

#print axioms determinant_ne_zero
#print axioms four_nonzero_relation
#print axioms exists_unique_zero_coefficient
end
end FourCorner.HpAxisQuadrics
