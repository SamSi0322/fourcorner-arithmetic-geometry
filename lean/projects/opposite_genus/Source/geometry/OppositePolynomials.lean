import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.Linarith

/-!
The actual three radicands in Proposition `ell-opposite-genus`.
These polynomial statements supply the six distinct simple finite zeros;
they do not assert connectedness or the genus of the associated cover.
-/
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false

noncomputable section
open Polynomial
namespace FourCorner.OppositePolynomials
variable {K : Type*} [Field K] [CharZero K]

def A (mu nu : K) : K := 2 * nu ^ 2 - mu ^ 2
def B (mu nu : K) : K := 4 * nu ^ 2 - mu ^ 2
def S (mu nu : K) : K := 2 * nu ^ 2 + mu ^ 2

def fZero (mu nu : K) : K[X] := X ^ 2 + C (2 * A mu nu * nu ^ 2)
def fPlus (mu nu : K) : K[X] := (X + C (A mu nu)) ^ 2 + C (2 * A mu nu * mu ^ 2)
def fMinus (mu nu : K) : K[X] := (X - C (A mu nu)) ^ 2 + C (2 * A mu nu * mu ^ 2)

def radicand (mu nu : K) : Fin 3 → K[X]
  | 0 => fZero mu nu
  | 1 => fPlus mu nu
  | 2 => fMinus mu nu

private theorem shifted_monic (s t : K) : ((X + C s)^2 + C t).Monic := by
  exact ((monic_X_add_C s).pow 2).add_of_left (degree_lt_degree (by simp))

private theorem shifted_degree (s t : K) : ((X + C s)^2 + C t).natDegree = 2 := by
  simp

private theorem shifted_separable (s t : K) (ht : t ≠ 0) :
    ((X + C s)^2 + C t).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K)
    ((X + C s)^2 + C t) (derivative ((X + C s)^2 + C t))).2
  intro z
  by_contra! h
  have hder : (2 : AlgebraicClosure K) * (z + algebraMap K (AlgebraicClosure K) s) = 0 := by
    simpa [derivative_pow, derivative_add, derivative_X, derivative_C] using h.2
  have hz := (mul_eq_zero.mp hder).resolve_left (by norm_num)
  have ht' : algebraMap K (AlgebraicClosure K) t ≠ 0 := (map_ne_zero (algebraMap K (AlgebraicClosure K))).2 ht
  apply ht'
  simpa [hz] using h.1

@[simp] theorem fZero_eval (mu nu z : K) :
    (fZero mu nu).eval z = z^2 + 2 * A mu nu * nu^2 := by simp [fZero]
@[simp] theorem fPlus_eval (mu nu z : K) :
    (fPlus mu nu).eval z = (z + A mu nu)^2 + 2 * A mu nu * mu^2 := by simp [fPlus]
@[simp] theorem fMinus_eval (mu nu z : K) :
    (fMinus mu nu).eval z = (z - A mu nu)^2 + 2 * A mu nu * mu^2 := by simp [fMinus]

theorem radicand_monic (mu nu : K) (i : Fin 3) : (radicand mu nu i).Monic := by
  fin_cases i
  · exact monic_X_pow_add_C _ (by decide)
  · exact shifted_monic _ _
  · simpa only [radicand, fMinus, sub_eq_add_neg, C_neg] using shifted_monic (-A mu nu) (2*A mu nu*mu^2)

theorem radicand_natDegree (mu nu : K) (i : Fin 3) : (radicand mu nu i).natDegree = 2 := by
  fin_cases i
  · exact natDegree_X_pow_add_C
  · exact shifted_degree _ _
  · simpa only [radicand, fMinus, sub_eq_add_neg, C_neg] using shifted_degree (-A mu nu) (2*A mu nu*mu^2)

theorem radicand_separable {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (i : Fin 3) : (radicand mu nu i).Separable := by
  have h2 : (2 : K) ≠ 0 := by norm_num
  fin_cases i
  · simpa only [radicand, fZero, C_0, add_zero] using shifted_separable (0 : K) (2*A mu nu*nu^2)
      (mul_ne_zero (mul_ne_zero h2 hA) (pow_ne_zero _ hnu))
  · exact shifted_separable _ _ (mul_ne_zero (mul_ne_zero h2 hA) (pow_ne_zero _ hmu))
  · simpa only [radicand, fMinus, sub_eq_add_neg, C_neg] using shifted_separable (-A mu nu) (2*A mu nu*mu^2)
      (mul_ne_zero (mul_ne_zero h2 hA) (pow_ne_zero _ hmu))

theorem radicand_squarefree {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (i : Fin 3) : Squarefree (radicand mu nu i) :=
  (radicand_separable hmu hnu hA i).squarefree

/-- The putative shared root is precisely the one computed in the manuscript. -/
theorem common_zero_plus_location {mu nu z : K} (hA : A mu nu ≠ 0)
    (h0 : (fZero mu nu).eval z = 0) (hp : (fPlus mu nu).eval z = 0) :
    z = -mu^2 / 2 := by
  simp only [fZero_eval, fPlus_eval] at h0 hp
  have h : A mu nu * (2*z + mu^2) = 0 := by
    dsimp [A] at *
    linear_combination hp - h0
  have hz := (mul_eq_zero.mp h).resolve_left hA
  apply (eq_div_iff (by norm_num : (2 : K) ≠ 0)).2
  linear_combination hz

theorem zero_at_common_location (mu nu : K) :
    (fZero mu nu).eval (-mu^2 / 2) = (B mu nu)^2 / 4 := by
  simp only [fZero_eval]
  dsimp [A, B]
  ring

theorem no_common_zero_plus {mu nu : K} (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0)
    (z : K) : ¬ ((fZero mu nu).eval z = 0 ∧ (fPlus mu nu).eval z = 0) := by
  rintro ⟨h0, hp⟩
  rw [common_zero_plus_location hA h0 hp, zero_at_common_location] at h0
  exact (div_ne_zero (pow_ne_zero 2 hB) (by norm_num)) h0

theorem no_common_zero_minus {mu nu : K} (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0)
    (z : K) : ¬ ((fZero mu nu).eval z = 0 ∧ (fMinus mu nu).eval z = 0) := by
  rintro ⟨h0, hm⟩
  apply no_common_zero_plus hA hB (-z)
  constructor
  · simpa using h0
  · simp only [fMinus_eval] at hm
    simp only [fPlus_eval]
    linear_combination hm

theorem no_common_plus_minus {mu nu : K} (hA : A mu nu ≠ 0) (hS : S mu nu ≠ 0)
    (z : K) : ¬ ((fPlus mu nu).eval z = 0 ∧ (fMinus mu nu).eval z = 0) := by
  rintro ⟨hp, hm⟩
  simp only [fPlus_eval, fMinus_eval] at hp hm
  have h : (4 * A mu nu) * z = 0 := by linear_combination hp - hm
  have hz : z = 0 := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hA)
  have hprod : A mu nu * S mu nu = 0 := by
    rw [hz] at hp
    dsimp [A, S] at *
    linear_combination hp
  exact mul_ne_zero hA hS hprod

@[simp] theorem A_map {L : Type*} [Field L] [CharZero L] (phi : K →+* L) (mu nu : K) :
    A (phi mu) (phi nu) = phi (A mu nu) := by simp [A, map_ofNat]
@[simp] theorem B_map {L : Type*} [Field L] [CharZero L] (phi : K →+* L) (mu nu : K) :
    B (phi mu) (phi nu) = phi (B mu nu) := by simp [B, map_ofNat]
@[simp] theorem S_map {L : Type*} [Field L] [CharZero L] (phi : K →+* L) (mu nu : K) :
    S (phi mu) (phi nu) = phi (S mu nu) := by simp [S, map_ofNat]

private theorem aeval_fZero {L : Type*} [Field L] [CharZero L] [Algebra K L]
    (mu nu : K) (z : L) :
    aeval z (fZero mu nu) = (fZero (algebraMap K L mu) (algebraMap K L nu)).eval z := by
  simp [fZero, A, map_ofNat]
private theorem aeval_fPlus {L : Type*} [Field L] [CharZero L] [Algebra K L]
    (mu nu : K) (z : L) :
    aeval z (fPlus mu nu) = (fPlus (algebraMap K L mu) (algebraMap K L nu)).eval z := by
  simp [fPlus, A, map_ofNat]
private theorem aeval_fMinus {L : Type*} [Field L] [CharZero L] [Algebra K L]
    (mu nu : K) (z : L) :
    aeval z (fMinus mu nu) = (fMinus (algebraMap K L mu) (algebraMap K L nu)).eval z := by
  simp [fMinus, A, map_ofNat]

theorem coprime_zero_plus {mu nu : K} (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) :
    IsCoprime (fZero mu nu) (fPlus mu nu) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).2
  intro z
  rw [aeval_fZero, aeval_fPlus]
  apply not_and_or.mp
  exact no_common_zero_plus (by simpa using (map_ne_zero (algebraMap K (AlgebraicClosure K))).2 hA)
    (by simpa using (map_ne_zero (algebraMap K (AlgebraicClosure K))).2 hB) z

theorem coprime_zero_minus {mu nu : K} (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) :
    IsCoprime (fZero mu nu) (fMinus mu nu) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).2
  intro z
  rw [aeval_fZero, aeval_fMinus]
  apply not_and_or.mp
  exact no_common_zero_minus (by simpa using (map_ne_zero (algebraMap K (AlgebraicClosure K))).2 hA)
    (by simpa using (map_ne_zero (algebraMap K (AlgebraicClosure K))).2 hB) z

theorem coprime_plus_minus {mu nu : K} (hA : A mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    IsCoprime (fPlus mu nu) (fMinus mu nu) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).2
  intro z
  rw [aeval_fPlus, aeval_fMinus]
  apply not_and_or.mp
  exact no_common_plus_minus (by simpa using (map_ne_zero (algebraMap K (AlgebraicClosure K))).2 hA)
    (by simpa using (map_ne_zero (algebraMap K (AlgebraicClosure K))).2 hS) z

theorem radicand_pairwise_coprime {mu nu : K}
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    Pairwise (fun i j : Fin 3 => IsCoprime (radicand mu nu i) (radicand mu nu j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact coprime_zero_plus hA hB
  · exact coprime_zero_minus hA hB
  · exact (coprime_zero_plus hA hB).symm
  · exact (hij rfl).elim
  · exact coprime_plus_minus hA hS
  · exact (coprime_zero_minus hA hB).symm
  · exact (coprime_plus_minus hA hS).symm
  · exact (hij rfl).elim

/-- Convenient two-index form of the pairwise coprimality theorem. -/
theorem radicand_isCoprime {mu nu : K}
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0)
    {i j : Fin 3} (hij : i ≠ j) : IsCoprime (radicand mu nu i) (radicand mu nu j) :=
  radicand_pairwise_coprime hA hB hS hij

theorem radicand_not_isUnit (mu nu : K) (i : Fin 3) : ¬ IsUnit (radicand mu nu i) := by
  intro hu
  have heq := (radicand_monic mu nu i).eq_one_of_isUnit hu
  have hd := radicand_natDegree mu nu i
  rw [heq, natDegree_one] at hd
  contradiction

/-- The roots of each actual quadratic, with multiplicity forgotten. -/
def rootSet (mu nu : K) (i : Fin 3) : Finset K := by
  classical
  exact (radicand mu nu i).roots.toFinset

@[simp] theorem mem_rootSet (mu nu z : K) (i : Fin 3) :
    z ∈ rootSet mu nu i ↔ (radicand mu nu i).eval z = 0 := by
  classical
  simp only [rootSet, Multiset.mem_toFinset, mem_roots (radicand_monic mu nu i).ne_zero, IsRoot]

theorem rootSets_pairwise_disjoint {mu nu : K}
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    Pairwise (fun i j : Fin 3 => Disjoint (rootSet mu nu i) (rootSet mu nu j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro z hzi hzj
  have h := aeval_ne_zero_of_isCoprime (radicand_pairwise_coprime hA hB hS hij) z
  simp only [aeval_def, Algebra.algebraMap_self, eval₂_id] at h
  exact h.elim (fun hn => hn ((mem_rootSet mu nu z i).1 hzi))
    (fun hn => hn ((mem_rootSet mu nu z j).1 hzj))

theorem rootMultiplicity_eq_one {mu nu z : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (i : Fin 3) (hz : (radicand mu nu i).eval z = 0) :
    (radicand mu nu i).rootMultiplicity z = 1 := by
  apply Nat.le_antisymm (rootMultiplicity_le_one_of_separable (radicand_separable hmu hnu hA i) z)
  exact (rootMultiplicity_pos (radicand_monic mu nu i).ne_zero).2 hz

theorem rootSet_card [IsAlgClosed K] {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (i : Fin 3) : (rootSet mu nu i).card = 2 := by
  classical
  rw [rootSet, Multiset.toFinset_card_of_nodup (nodup_roots (radicand_separable hmu hnu hA i)),
    IsAlgClosed.card_roots_eq_natDegree, radicand_natDegree]

/-- Each root belongs to just its own quadratic and has multiplicity exactly one. -/
theorem exists_private_simple_root [IsAlgClosed K] {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) (i : Fin 3) :
    ∃ z : K, (radicand mu nu i).eval z = 0 ∧
      (radicand mu nu i).rootMultiplicity z = 1 ∧
      ∀ j : Fin 3, j ≠ i → (radicand mu nu j).eval z ≠ 0 := by
  have hc := rootSet_card hmu hnu hA i
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < (rootSet mu nu i).card by omega)
  have hz0 := (mem_rootSet mu nu z i).1 hz
  refine ⟨z, hz0, rootMultiplicity_eq_one hmu hnu hA i hz0, ?_⟩
  intro j hji hzj
  exact (Finset.disjoint_left.mp (rootSets_pairwise_disjoint hA hB hS hji))
    ((mem_rootSet mu nu z j).2 hzj) hz

/-- All finite branch candidates, as the union of the three actual root sets. -/
def allRoots (mu nu : K) : Finset K := by
  classical
  exact rootSet mu nu 0 ∪ rootSet mu nu 1 ∪ rootSet mu nu 2

/-- Precisely six different zeros, not merely a formal count with multiplicity. -/
theorem allRoots_card [IsAlgClosed K] {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) : (allRoots mu nu).card = 6 := by
  classical
  have h01 := rootSets_pairwise_disjoint hA hB hS (i := 0) (j := 1) (by decide)
  have h02 := rootSets_pairwise_disjoint hA hB hS (i := 0) (j := 2) (by decide)
  have h12 := rootSets_pairwise_disjoint hA hB hS (i := 1) (j := 2) (by decide)
  rw [allRoots, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h02, h12⟩),
    Finset.card_union_of_disjoint h01, rootSet_card hmu hnu hA, rootSet_card hmu hnu hA,
    rootSet_card hmu hnu hA]

/-- Rational parameters cannot have ratio equal to a square root of two. -/
theorem rational_A_ne_zero (mu nu : ℚ) (hnu : nu ≠ 0) : A mu nu ≠ 0 := by
  intro hz
  have hns : ¬ IsSquare (2 : ℚ) := by norm_num
  apply hns
  refine ⟨mu / nu, ?_⟩
  field_simp
  dsimp [A] at hz
  nlinarith [hz]

theorem rational_B_ne_zero (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) : B mu nu ≠ 0 := by
  intro hz
  have hsq : (mu / nu)^2 = 4 := by
    field_simp
    dsimp [B] at hz
    nlinarith [hz]
  nlinarith [mul_pos hpos (sub_pos.mpr hlt)]

theorem rational_S_ne_zero (mu nu : ℚ) (hnu : nu ≠ 0) : S mu nu ≠ 0 := by
  have hn : 0 < nu^2 := sq_pos_of_ne_zero hnu
  dsimp [S]
  nlinarith [sq_nonneg mu]

/-- The finite-zero portion of the manuscript's argument, with all algebraic
nondegeneracy conditions derived from its rational parameter range. -/
theorem rational_finite_zero_data [IsAlgClosed K] (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) :
    let m := algebraMap ℚ K mu
    let n := algebraMap ℚ K nu
    (∀ i : Fin 3, (radicand m n i).Monic ∧ (radicand m n i).natDegree = 2 ∧
      (radicand m n i).Separable ∧ Squarefree (radicand m n i) ∧
      (rootSet m n i).card = 2) ∧
    Pairwise (fun i j : Fin 3 => IsCoprime (radicand m n i) (radicand m n j)) ∧
    Pairwise (fun i j : Fin 3 => Disjoint (rootSet m n i) (rootSet m n j)) ∧
    (allRoots m n).card = 6 := by
  dsimp only
  have hmu : mu ≠ 0 := by intro hz; simp [hz] at hpos
  have hm : algebraMap ℚ K mu ≠ 0 := (map_ne_zero (algebraMap ℚ K)).2 hmu
  have hn : algebraMap ℚ K nu ≠ 0 := (map_ne_zero (algebraMap ℚ K)).2 hnu
  have ha : A (algebraMap ℚ K mu) (algebraMap ℚ K nu) ≠ 0 := by
    simpa only [A_map] using (map_ne_zero (algebraMap ℚ K)).2 (rational_A_ne_zero mu nu hnu)
  have hb : B (algebraMap ℚ K mu) (algebraMap ℚ K nu) ≠ 0 := by
    simpa only [B_map] using (map_ne_zero (algebraMap ℚ K)).2 (rational_B_ne_zero mu nu hnu hpos hlt)
  have hs : S (algebraMap ℚ K mu) (algebraMap ℚ K nu) ≠ 0 := by
    simpa only [S_map] using (map_ne_zero (algebraMap ℚ K)).2 (rational_S_ne_zero mu nu hnu)
  refine ⟨?_, radicand_pairwise_coprime ha hb hs, rootSets_pairwise_disjoint ha hb hs,
    allRoots_card hm hn ha hb hs⟩
  intro i
  exact ⟨radicand_monic _ _ i, radicand_natDegree _ _ i, radicand_separable hm hn ha i,
    radicand_squarefree hm hn ha i, rootSet_card hm hn ha i⟩

end FourCorner.OppositePolynomials

#print axioms FourCorner.OppositePolynomials.radicand_monic
#print axioms FourCorner.OppositePolynomials.radicand_natDegree
#print axioms FourCorner.OppositePolynomials.radicand_separable
#print axioms FourCorner.OppositePolynomials.radicand_squarefree
#print axioms FourCorner.OppositePolynomials.common_zero_plus_location
#print axioms FourCorner.OppositePolynomials.zero_at_common_location
#print axioms FourCorner.OppositePolynomials.no_common_zero_plus
#print axioms FourCorner.OppositePolynomials.no_common_zero_minus
#print axioms FourCorner.OppositePolynomials.no_common_plus_minus
#print axioms FourCorner.OppositePolynomials.radicand_isCoprime
#print axioms FourCorner.OppositePolynomials.radicand_not_isUnit
#print axioms FourCorner.OppositePolynomials.rootSets_pairwise_disjoint
#print axioms FourCorner.OppositePolynomials.rootMultiplicity_eq_one
#print axioms FourCorner.OppositePolynomials.rootSet_card
#print axioms FourCorner.OppositePolynomials.exists_private_simple_root
#print axioms FourCorner.OppositePolynomials.allRoots_card
#print axioms FourCorner.OppositePolynomials.rational_A_ne_zero
#print axioms FourCorner.OppositePolynomials.rational_B_ne_zero
#print axioms FourCorner.OppositePolynomials.rational_S_ne_zero
#print axioms FourCorner.OppositePolynomials.rational_finite_zero_data
