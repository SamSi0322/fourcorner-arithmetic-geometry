import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace FourCorner

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complete prescribed off-diagonal entries to a matrix over F₂ with zero
row sums. The original diagonal entries of `a` are not used. -/
def rowZeroMatrix (a : Matrix ι ι (ZMod 2)) : Matrix ι ι (ZMod 2) :=
  fun i j => if i = j then ∑ k ∈ Finset.univ.erase i, a i k else a i j

@[simp] lemma rowZeroMatrix_diagonal (a : Matrix ι ι (ZMod 2)) (i : ι) :
    rowZeroMatrix a i i = ∑ j ∈ Finset.univ.erase i, a i j := by
  simp [rowZeroMatrix]

lemma rowZeroMatrix_off_diagonal (a : Matrix ι ι (ZMod 2)) {i j : ι} (hij : i ≠ j) :
    rowZeroMatrix a i j = a i j := by
  simp [rowZeroMatrix, hij]

/-- The matrix equation is exactly the sum of off-diagonal contributions
weighted by the endpoint-bit differences, written as sums in F₂. -/
lemma rowZeroMatrix_mulVec (a : Matrix ι ι (ZMod 2)) (e : ι → ZMod 2) (i : ι) :
    (rowZeroMatrix a).mulVec e i =
      ∑ j ∈ Finset.univ.erase i, a i j * (e j + e i) := by
  change (∑ j, rowZeroMatrix a i j * e j) = _
  rw [← Finset.sum_erase_add Finset.univ (fun j => rowZeroMatrix a i j * e j)
    (Finset.mem_univ i)]
  rw [rowZeroMatrix_diagonal, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
  rw [rowZeroMatrix_off_diagonal a hij]
  ring

/-- The all-ones vector lies in the kernel of every completed matrix. -/
lemma rowZeroMatrix_mulVec_one (a : Matrix ι ι (ZMod 2)) :
    (rowZeroMatrix a).mulVec (1 : ι → ZMod 2) = 0 := by
  funext i
  rw [rowZeroMatrix_mulVec]
  simp [CharTwo.add_self_eq_zero]

lemma rowZeroMatrix_row_sum (a : Matrix ι ι (ZMod 2)) (i : ι) :
    ∑ j, rowZeroMatrix a i j = 0 := by
  have h := congrFun (rowZeroMatrix_mulVec_one a) i
  simpa [Matrix.mulVec, dotProduct] using h

omit [DecidableEq ι] in
lemma matrix_mulVec_one_of_row_sums_zero (A : Matrix ι ι (ZMod 2))
    (hrow : ∀ i, ∑ j, A i j = 0) : A.mulVec (1 : ι → ZMod 2) = 0 := by
  funext i
  simpa [Matrix.mulVec, dotProduct] using hrow i

lemma zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [DecidableEq ι] in
/-- Rank-nullity uses the actual matrix rank. If a nonempty square F₂ matrix
has zero row sums and rank one below its size, its only kernel vectors are
the zero and all-ones vectors. -/
theorem matrix_kernel_eq_zero_or_one_of_rank [Nonempty ι]
    (A : Matrix ι ι (ZMod 2)) (hrow : ∀ i, ∑ j, A i j = 0)
    (hrank : A.rank = Fintype.card ι - 1) (e : ι → ZMod 2) :
    A.mulVec e = 0 ↔ e = 0 ∨ e = 1 := by
  classical
  have hones := matrix_mulVec_one_of_row_sums_zero A hrow
  have hdim := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  change A.rank + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
    Module.finrank (ZMod 2) (ι → ZMod 2) at hdim
  rw [Module.finrank_pi, hrank] at hdim
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hker : Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = 1 := by omega
  let ones : LinearMap.ker A.mulVecLin :=
    ⟨1, by simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hones⟩
  have hones_ne : ones ≠ 0 := by
    intro hz
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hi := congrFun (congrArg Subtype.val hz) i
    exact one_ne_zero hi
  constructor
  · intro he
    let v : LinearMap.ker A.mulVecLin :=
      ⟨e, by simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using he⟩
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hker hones_ne v
    have hcv : c • (1 : ι → ZMod 2) = e := congrArg Subtype.val hc
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · left
      simpa using hcv.symm
    · right
      simpa using hcv.symm
  · rintro (rfl | rfl)
    · exact Matrix.mulVec_zero A
    · exact hones

/-- The finite-index version states the size positivity explicitly. -/
theorem matrix_kernel_eq_zero_or_one {r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin r) (Fin r) (ZMod 2)) (hrow : ∀ i, ∑ j, A i j = 0)
    (hrank : A.rank = r - 1) (e : Fin r → ZMod 2) :
    A.mulVec e = 0 ↔ e = 0 ∨ e = 1 := by
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact matrix_kernel_eq_zero_or_one_of_rank A hrow (by simpa using hrank) e

/-- In particular the rank test applies to the prescribed row-zero
completion without requiring any additional row-sum hypotheses. -/
theorem rowZeroMatrix_kernel_eq_zero_or_one [Nonempty ι]
    (a : Matrix ι ι (ZMod 2)) (hrank : (rowZeroMatrix a).rank = Fintype.card ι - 1)
    (e : ι → ZMod 2) : (rowZeroMatrix a).mulVec e = 0 ↔ e = 0 ∨ e = 1 :=
  matrix_kernel_eq_zero_or_one_of_rank _ (rowZeroMatrix_row_sum a) hrank e

end FourCorner

#print axioms FourCorner.rowZeroMatrix_mulVec
#print axioms FourCorner.rowZeroMatrix_mulVec_one
#print axioms FourCorner.matrix_kernel_eq_zero_or_one
#print axioms FourCorner.rowZeroMatrix_kernel_eq_zero_or_one
