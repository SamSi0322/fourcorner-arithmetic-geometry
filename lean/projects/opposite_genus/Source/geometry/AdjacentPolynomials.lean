import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.Linarith

/-!
The two actual adjacent-source quartics in Proposition `ell-adjacent-genus`,
obtained by the rational parametrization of its conic. This file proves
polynomial and finite-root facts; it does not assert a curve's genus.
-/
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
noncomputable section
open Polynomial
namespace FourCorner.AdjacentPolynomials
variable {K : Type*} [Field K] [CharZero K]

def D (c : K) : K[X] := C (c^2) * X^2 + C (c^2-1)
def U (c : K) : K[X] := C c * (C (c^2) * X^2 - C (c^2-1))
def V (c : K) : K[X] := C (2*c*(c^2-1)) * X

def g2 (c : K) : K[X] := (U c + D c)^2 + (V c - 2*D c)^2
def g3 (c : K) : K[X] := (U c - D c)^2 + (V c - 2*D c)^2

def radicand (c : K) : Fin 2 → K[X]
  | 0 => g2 c
  | 1 => g3 c

/-- The explicit exceptional factors in the polynomial calculations. -/
structure Admissible (c : K) : Prop where
  c_ne_zero : c ≠ 0
  conic_ne_zero : c^2 - 1 ≠ 0
  tangency_ne_zero : c^4 - 6*c^2 + 1 ≠ 0
  intersection_ne_zero : c^4 - 8*c^2 + 32 ≠ 0
  leading_plus_ne_zero : c^2 + 2*c + 5 ≠ 0
  leading_minus_ne_zero : c^2 - 2*c + 5 ≠ 0

theorem conic_identity (c : K) :
    C (c^2-1) * (U c)^2 + C (c^2) * (V c)^2 -
      C (c^2*(c^2-1)) * (D c)^2 = 0 := by
  simp [U, V, D, map_ofNat]
  ring

/-- Expanded quartic, with the change of variable x = c T kept visible. -/
def P (c x : K[X]) : K[X] :=
  (c^2+2*c+5)*x^4 - 8*(c^2-1)*x^3 + 2*(c^2-1)*(c^2+3)*x^2 -
    8*(c^2-1)^2*x + (c^2-1)^2*(c^2-2*c+5)

theorem g2_expansion (c : K) : g2 c = P (C c) (C c * X) := by
  simp [g2, P, U, V, D, map_ofNat]
  ring

theorem g3_expansion (c : K) : g3 c = P (-C c) (C c * X) := by
  simp [g3, P, U, V, D, map_ofNat]
  ring

private theorem quartic_natDegree (a b d e f : K) (ha : a ≠ 0) :
    (C a*X^4 + C b*X^3 + C d*X^2 + C e*X + C f).natDegree = 4 := by
  compute_degree!

private theorem coprime_of_combination {p q r s : K[X]} {a : K}
    (ha : a ≠ 0) (heq : r*p + s*q = C a) : IsCoprime p q := by
  refine ⟨C a⁻¹*r, C a⁻¹*s, ?_⟩
  calc
    C a⁻¹*r*p + C a⁻¹*s*q = C a⁻¹*(r*p+s*q) := by ring
    _ = 1 := by rw [heq, ← map_mul, inv_mul_cancel₀ ha, map_one]

private def certF (z : K[X]) := z^6-2*z^5-29*z^4-20*z^3+43*z^2+30*z+9
private def certJ (z : K[X]) := z^7+11*z^6-7*z^5-157*z^4-89*z^3+397*z^2+351*z+69
private def certK (z : K[X]) := z^7-7*z^6-35*z^5-3*z^4+79*z^3-25*z^2-61*z-13
private def certM (z : K[X]) := z^6+2*z^5-33*z^4-108*z^3-61*z^2+98*z+5
private def certN (z : K[X]) := (z+1)*(z^6+6*z^5-21*z^4-132*z^3+27*z^2+230*z+49)
private def sepA (z x : K[X]) :=
  -4*(z^2+2*z+5)*certF z*x^2 + 4*(z^2-1)*certJ z*x - 8*(z^2-1)*certK z
private def sepB (z x : K[X]) :=
  (z^2+2*z+5)*certF z*x^3 - (z^2-1)*(certJ z+2*certF z)*x^2 +
    (z^2-1)^2*certM z*x - (z^2-1)^2*certN z

/-- An exact polynomial Bézout certificate for the first quartic and its derivative. -/
private theorem g2_derivative_certificate (c : K) :
    (C c * sepA (C c) (C c*X)) * g2 c + sepB (C c) (C c*X) * (g2 c).derivative =
      C (128*c*(c^2-1)^3*(c^4-6*c^2+1)^2) := by
  simp [g2, U, V, D, sepA, sepB, certF, certJ, certK, certM, certN,
    derivative_pow, derivative_mul, derivative_add, derivative_sub, map_ofNat]
  ring

private theorem g3_derivative_certificate (c : K) :
    (C c * sepA (-C c) (C c*X)) * g3 c + sepB (-C c) (C c*X) * (g3 c).derivative =
      C (128*c*(c^2-1)^3*(c^4-6*c^2+1)^2) := by
  simp [g3, U, V, D, sepA, sepB, certF, certJ, certK, certM, certN,
    derivative_pow, derivative_mul, derivative_add, derivative_sub, map_ofNat]
  ring

private def denomQuot (c s : K) : K[X] :=
  C (c^2+2*s*c+5)*D c - 4*C (c^2-1)*(1+C (s*c)+2*C c*X)

private theorem g2_denominator_certificate (c : K) :
    1 * g2 c + (-denomQuot c 1) * D c = C (4*(c^2-1)^2) := by
  simp [g2, U, V, D, denomQuot, map_ofNat]
  ring

private theorem g3_denominator_certificate (c : K) :
    1 * g3 c + (-denomQuot c (-1)) * D c = C (4*(c^2-1)^2) := by
  simp [g3, U, V, D, denomQuot, map_ofNat]
  ring

private def Q (c : K) : K[X] := C (c^2)*X^2 - C (c^2-1)
private def pairM (c : K) : K[X] := C (c^2+4)+4*C c*X
private def pairK (c : K) : K[X] :=
  C (c^2+2*c+5)*Q c + 4*C (c^2-1)*(C (c^2+4+c)-2*C c*X)
private def pairB (c : K) : K[X] := 64*C (c^2-1)^2 - pairM c*pairK c

private theorem pair_certificate (c : K) :
    (16*C c*C (c^2-1)^2*pairM c + 4*C c*pairB c*Q c - pairB c*denomQuot c 1)*g2 c +
      (pairB c*denomQuot c 1)*g3 c = C (64*c*(c^2-1)^4*(c^4-8*c^2+32)) := by
  simp [g2, g3, U, V, D, pairB, pairM, pairK, Q, denomQuot, map_ofNat]
  ring

theorem g2_separable {c : K} (h : Admissible c) : (g2 c).Separable := by
  exact coprime_of_combination
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h.c_ne_zero)
      (pow_ne_zero _ h.conic_ne_zero)) (pow_ne_zero _ h.tangency_ne_zero))
    (g2_derivative_certificate c)

theorem g3_separable {c : K} (h : Admissible c) : (g3 c).Separable := by
  exact coprime_of_combination
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h.c_ne_zero)
      (pow_ne_zero _ h.conic_ne_zero)) (pow_ne_zero _ h.tangency_ne_zero))
    (g3_derivative_certificate c)

theorem g2_coprime_g3 {c : K} (h : Admissible c) : IsCoprime (g2 c) (g3 c) := by
  exact coprime_of_combination
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h.c_ne_zero)
      (pow_ne_zero _ h.conic_ne_zero)) h.intersection_ne_zero) (pair_certificate c)

theorem g2_coprime_D {c : K} (h : Admissible c) : IsCoprime (g2 c) (D c) :=
  coprime_of_combination (mul_ne_zero (by norm_num) (pow_ne_zero _ h.conic_ne_zero))
    (g2_denominator_certificate c)

theorem g3_coprime_D {c : K} (h : Admissible c) : IsCoprime (g3 c) (D c) :=
  coprime_of_combination (mul_ne_zero (by norm_num) (pow_ne_zero _ h.conic_ne_zero))
    (g3_denominator_certificate c)

private theorem P_natDegree (c d : K) (hd : d ≠ 0) (hc : c^2+2*c+5 ≠ 0) :
    (P (C c) (C d*X)).natDegree = 4 := by
  have heq : P (C c) (C d*X) =
      C ((c^2+2*c+5)*d^4)*X^4 + C (-8*(c^2-1)*d^3)*X^3 +
      C (2*(c^2-1)*(c^2+3)*d^2)*X^2 + C (-8*(c^2-1)^2*d)*X +
      C ((c^2-1)^2*(c^2-2*c+5)) := by
    simp [P, map_ofNat]
    ring
  rw [heq]
  exact quartic_natDegree _ _ _ _ _ (mul_ne_zero hc (pow_ne_zero _ hd))

theorem g2_natDegree {c : K} (h : Admissible c) : (g2 c).natDegree = 4 := by
  rw [g2_expansion]
  exact P_natDegree c c h.c_ne_zero h.leading_plus_ne_zero

theorem g3_natDegree {c : K} (h : Admissible c) : (g3 c).natDegree = 4 := by
  rw [g3_expansion, ← C_neg]
  apply P_natDegree (-c) c h.c_ne_zero
  have heq : (-c)^2+2*(-c)+5 = c^2-2*c+5 := by ring
  rw [heq]
  exact h.leading_minus_ne_zero

theorem D_natDegree {c : K} (h : Admissible c) : (D c).natDegree = 2 := by
  have hc : c^2 ≠ 0 := pow_ne_zero _ h.c_ne_zero
  unfold D
  compute_degree!
  exact h.c_ne_zero

theorem D_separable {c : K} (h : Admissible c) : (D c).Separable := by
  apply coprime_of_combination (mul_ne_zero (by norm_num : (2 : K) ≠ 0) h.conic_ne_zero)
    (r := 2) (s := -X)
  simp [D, derivative_pow, derivative_mul, derivative_add, map_ofNat]
  ring

theorem D_ne_zero {c : K} (h : Admissible c) : D c ≠ 0 := (D_separable h).ne_zero

theorem radicand_natDegree {c : K} (h : Admissible c) (i : Fin 2) :
    (radicand c i).natDegree = 4 := by
  fin_cases i
  · exact g2_natDegree h
  · exact g3_natDegree h

theorem radicand_separable {c : K} (h : Admissible c) (i : Fin 2) :
    (radicand c i).Separable := by
  fin_cases i
  · exact g2_separable h
  · exact g3_separable h

theorem radicand_ne_zero {c : K} (h : Admissible c) (i : Fin 2) : radicand c i ≠ 0 :=
  (radicand_separable h i).ne_zero

theorem radicand_not_isUnit {c : K} (h : Admissible c) (i : Fin 2) :
    ¬ IsUnit (radicand c i) := by
  apply not_isUnit_of_natDegree_pos
  rw [radicand_natDegree h i]
  decide

theorem radicand_squarefree {c : K} (h : Admissible c) (i : Fin 2) :
    Squarefree (radicand c i) := (radicand_separable h i).squarefree

theorem radicand_isCoprime {c : K} (h : Admissible c) {i j : Fin 2} (hij : i ≠ j) :
    IsCoprime (radicand c i) (radicand c j) := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact g2_coprime_g3 h
  · exact (g2_coprime_g3 h).symm
  · exact (hij rfl).elim

theorem radicand_coprime_D {c : K} (h : Admissible c) (i : Fin 2) :
    IsCoprime (radicand c i) (D c) := by
  fin_cases i
  · exact g2_coprime_D h
  · exact g3_coprime_D h

def rootSet (c : K) (i : Fin 2) : Finset K := by
  classical
  exact (radicand c i).roots.toFinset

theorem mem_rootSet {c : K} (h : Admissible c) (z : K) (i : Fin 2) :
    z ∈ rootSet c i ↔ (radicand c i).eval z = 0 := by
  classical
  simp only [rootSet, Multiset.mem_toFinset, mem_roots (radicand_ne_zero h i), IsRoot]

theorem rootSets_pairwise_disjoint {c : K} (h : Admissible c) :
    Pairwise (fun i j : Fin 2 => Disjoint (rootSet c i) (rootSet c j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro z hzi hzj
  have hh := aeval_ne_zero_of_isCoprime (radicand_isCoprime h hij) z
  simp only [aeval_def, Algebra.algebraMap_self, eval₂_id] at hh
  exact hh.elim (fun hn => hn ((mem_rootSet h z i).1 hzi))
    (fun hn => hn ((mem_rootSet h z j).1 hzj))

theorem root_not_denominator_root {c z : K} (h : Admissible c) (i : Fin 2)
    (hz : (radicand c i).eval z = 0) : (D c).eval z ≠ 0 := by
  have hh := aeval_ne_zero_of_isCoprime (radicand_coprime_D h i) z
  simp only [aeval_def, Algebra.algebraMap_self, eval₂_id] at hh
  exact hh.resolve_left (not_not.mpr hz)

theorem rootMultiplicity_eq_one {c z : K} (h : Admissible c) (i : Fin 2)
    (hz : (radicand c i).eval z = 0) : (radicand c i).rootMultiplicity z = 1 := by
  apply Nat.le_antisymm (rootMultiplicity_le_one_of_separable (radicand_separable h i) z)
  exact (rootMultiplicity_pos (radicand_ne_zero h i)).2 hz

theorem rootSet_card [IsAlgClosed K] {c : K} (h : Admissible c) (i : Fin 2) :
    (rootSet c i).card = 4 := by
  classical
  rw [rootSet, Multiset.toFinset_card_of_nodup (nodup_roots (radicand_separable h i)),
    IsAlgClosed.card_roots_eq_natDegree, radicand_natDegree h]

theorem exists_private_simple_root [IsAlgClosed K] {c : K} (h : Admissible c) (i : Fin 2) :
    ∃ z : K, (radicand c i).eval z = 0 ∧ (radicand c i).rootMultiplicity z = 1 ∧
      (D c).eval z ≠ 0 ∧ ∀ j : Fin 2, j ≠ i → (radicand c j).eval z ≠ 0 := by
  have hc := rootSet_card h i
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < (rootSet c i).card by omega)
  have hz0 := (mem_rootSet h z i).1 hz
  refine ⟨z, hz0, rootMultiplicity_eq_one h i hz0, root_not_denominator_root h i hz0, ?_⟩
  intro j hji hzj
  exact (Finset.disjoint_left.mp (rootSets_pairwise_disjoint h hji))
    ((mem_rootSet h z j).2 hzj) hz

def allRoots (c : K) : Finset K := by
  classical
  exact rootSet c 0 ∪ rootSet c 1

/-- Eight distinct simple numerator zeros on the parameter line. -/
theorem allRoots_card [IsAlgClosed K] {c : K} (h : Admissible c) : (allRoots c).card = 8 := by
  classical
  rw [allRoots, Finset.card_union_of_disjoint (rootSets_pairwise_disjoint h (by decide :
    (0 : Fin 2) ≠ 1)), rootSet_card h, rootSet_card h]

theorem rational_admissible_self (c : ℚ) (hc : 0 < c) (hc1 : c ≠ 1) : Admissible c := by
  refine ⟨ne_of_gt hc, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    have hs : c^2 = 1 := by linarith
    rcases sq_eq_one_iff.mp hs with h | h
    · exact hc1 h
    · linarith
  · intro hz
    have hns : ¬ IsSquare (8 : ℚ) := by norm_num
    apply hns
    refine ⟨c^2-3, ?_⟩
    nlinarith [hz]
  · nlinarith [sq_nonneg (c^2-4)]
  · nlinarith [sq_nonneg (c+1)]
  · nlinarith [sq_nonneg (c-1)]

theorem Admissible.map {L : Type*} [Field L] [CharZero L]
    {c : K} (h : Admissible c) (phi : K →+* L) : Admissible (phi c) := by
  constructor
  · exact (map_ne_zero phi).2 h.c_ne_zero
  · simpa [map_ofNat] using (map_ne_zero phi).2 h.conic_ne_zero
  · simpa [map_ofNat] using (map_ne_zero phi).2 h.tangency_ne_zero
  · simpa [map_ofNat] using (map_ne_zero phi).2 h.intersection_ne_zero
  · simpa [map_ofNat] using (map_ne_zero phi).2 h.leading_plus_ne_zero
  · simpa [map_ofNat] using (map_ne_zero phi).2 h.leading_minus_ne_zero

theorem rational_admissible (c : ℚ) (hc : 0 < c) (hc1 : c ≠ 1) :
    Admissible (algebraMap ℚ K c) := (rational_admissible_self c hc hc1).map (algebraMap ℚ K)

/-- The polynomial and finite-root claims specialized to the manuscript's full
rational parameter range, without assuming any of the desired polynomial facts. -/
theorem rational_finite_zero_data [IsAlgClosed K] (c : ℚ) (hc : 0 < c) (hc1 : c ≠ 1) :
    let k := algebraMap ℚ K c
    (D k).natDegree = 2 ∧ (D k).Separable ∧
    (∀ i : Fin 2, (radicand k i).natDegree = 4 ∧ (radicand k i).Separable ∧
      Squarefree (radicand k i) ∧ IsCoprime (radicand k i) (D k) ∧ (rootSet k i).card = 4) ∧
    Pairwise (fun i j : Fin 2 => IsCoprime (radicand k i) (radicand k j)) ∧
    Pairwise (fun i j : Fin 2 => Disjoint (rootSet k i) (rootSet k j)) ∧
    (allRoots k).card = 8 := by
  dsimp only
  have h := rational_admissible (K := K) c hc hc1
  refine ⟨D_natDegree h, D_separable h, ?_, fun _ _ hij => radicand_isCoprime h hij,
    rootSets_pairwise_disjoint h, allRoots_card h⟩
  intro i
  exact ⟨radicand_natDegree h i, radicand_separable h i, radicand_squarefree h i,
    radicand_coprime_D h i, rootSet_card h i⟩

end FourCorner.AdjacentPolynomials

#print axioms FourCorner.AdjacentPolynomials.conic_identity
#print axioms FourCorner.AdjacentPolynomials.g2_separable
#print axioms FourCorner.AdjacentPolynomials.g3_separable
#print axioms FourCorner.AdjacentPolynomials.g2_coprime_g3
#print axioms FourCorner.AdjacentPolynomials.g2_coprime_D
#print axioms FourCorner.AdjacentPolynomials.g3_coprime_D
#print axioms FourCorner.AdjacentPolynomials.g2_natDegree
#print axioms FourCorner.AdjacentPolynomials.g3_natDegree
#print axioms FourCorner.AdjacentPolynomials.D_natDegree
#print axioms FourCorner.AdjacentPolynomials.D_separable
#print axioms FourCorner.AdjacentPolynomials.D_ne_zero
#print axioms FourCorner.AdjacentPolynomials.radicand_natDegree
#print axioms FourCorner.AdjacentPolynomials.radicand_separable
#print axioms FourCorner.AdjacentPolynomials.radicand_ne_zero
#print axioms FourCorner.AdjacentPolynomials.radicand_not_isUnit
#print axioms FourCorner.AdjacentPolynomials.radicand_squarefree
#print axioms FourCorner.AdjacentPolynomials.radicand_isCoprime
#print axioms FourCorner.AdjacentPolynomials.radicand_coprime_D
#print axioms FourCorner.AdjacentPolynomials.rootSets_pairwise_disjoint
#print axioms FourCorner.AdjacentPolynomials.root_not_denominator_root
#print axioms FourCorner.AdjacentPolynomials.rootMultiplicity_eq_one
#print axioms FourCorner.AdjacentPolynomials.rootSet_card
#print axioms FourCorner.AdjacentPolynomials.exists_private_simple_root
#print axioms FourCorner.AdjacentPolynomials.allRoots_card
#print axioms FourCorner.AdjacentPolynomials.rational_admissible_self
#print axioms FourCorner.AdjacentPolynomials.Admissible.map
#print axioms FourCorner.AdjacentPolynomials.rational_admissible
#print axioms FourCorner.AdjacentPolynomials.rational_finite_zero_data
