import OrderedKummer
import FourCorner.NineFlexGroup

open Polynomial WeierstrassCurve.Affine
namespace FourCorner.OrderedSplit
noncomputable section

/-- Fixed order of the three rational branch roots. -/
def splitRoots (A B : ℚ) : Fin 3 → ℚ := ![0, A, B]

theorem splitRoots_injective (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B) :
    Function.Injective (splitRoots A B) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [splitRoots]

/-- This is the literal cubic of the actual Weierstrass model. -/
theorem splitCurve_f_factorization (A B : ℚ) :
    (splitCurve A B).toAffine.f = ∏ i : Fin 3, (X - C (splitRoots A B i)) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [splitRoots, f, splitCurve]
  ring

instance splitCurve_charNeTwoNF (A B : ℚ) : (splitCurve A B).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

/-- Ellipticity from the explicit nonzero discriminant. -/
theorem splitCurve_isElliptic (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B) :
    (splitCurve A B).IsElliptic :=
  ⟨((splitCurve_discriminant_ne_zero_iff A B).mpr ⟨hA, hB, hAB⟩).isUnit⟩

/-- Ordered evaluation for the actual split cubic. -/
def splitEval (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B) :
    (splitCurve A B).toAffine.A ≃ₐ[ℚ] (Fin 3 → ℚ) :=
  orderedEval (splitRoots A B) (splitRoots_injective A B hA hB hAB)
    (splitCurve_f_factorization A B)

@[simp]
theorem splitEval_mk (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B)
    (q : ℚ[X]) (i : Fin 3) :
    splitEval A B hA hB hAB (AdjoinRoot.mk (splitCurve A B).toAffine.f q) i =
      q.eval (splitRoots A B i) := orderedEval_mk _ _ _ _ _

/-- The actual split-cubic Kummer homomorphism in root order `(0,A,B)`. -/
def splitDelta (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B) :
    Multiplicative (splitCurve A B).toAffine.Point →* (Fin 3 → Units.modPow ℚ 2) := by
  letI := splitCurve_isElliptic A B hA hB hAB
  exact orderedDelta (splitRoots A B) (splitRoots_injective A B hA hB hAB)
    (splitCurve_f_factorization A B)

theorem splitDelta_ker (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B) :
    (splitDelta A B hA hB hAB).ker =
      (nsmulAddMonoidHom (α := (splitCurve A B).toAffine.Point) 2).range.toSubgroup := by
  letI := splitCurve_isElliptic A B hA hB hAB
  exact orderedDelta_ker _ _ _

theorem splitDelta_eq_one_iff_double (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B)
    (P : (splitCurve A B).toAffine.Point) :
    splitDelta A B hA hB hAB (Multiplicative.ofAdd P) = 1 ↔
      ∃ Q : (splitCurve A B).toAffine.Point, 2 • Q = P := by
  letI := splitCurve_isElliptic A B hA hB hAB
  exact orderedDelta_eq_one_iff_double _ _ _ P

/-- For an ordinary point the complete signed row is `(x,x-A,x-B)`. -/
theorem splitDelta_some_of_nonroot (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B)
    {x y : ℚ} (hxy : (splitCurve A B).toAffine.Nonsingular x y)
    (hx : x ≠ 0) (hxA : x ≠ A) (hxB : x ≠ B) :
    splitDelta A B hA hB hAB (Multiplicative.ofAdd (Point.some x y hxy)) =
      ![scalarClass x hx, scalarClass (x - A) (sub_ne_zero.mpr hxA),
        scalarClass (x - B) (sub_ne_zero.mpr hxB)] := by
  letI := splitCurve_isElliptic A B hA hB hAB
  have hn : (splitCurve A B).toAffine.f.eval x ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := (eval_f_eq_zero_iff (splitRoots A B)
      (splitCurve_f_factorization A B) x).mp hz
    fin_cases i <;> simp_all [splitRoots]
  ext i
  change orderedDelta (splitRoots A B) (splitRoots_injective A B hA hB hAB)
    (splitCurve_f_factorization A B) _ i = _
  rw [orderedDelta_some_of_nonroot _ _ _ hxy hn]
  fin_cases i <;> simp [splitRoots]

/-- Complete ordered signed row at the root `0`. -/
theorem splitDelta_at_zero (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B)
    (hxy : (splitCurve A B).toAffine.Nonsingular 0 0) :
    splitDelta A B hA hB hAB (Multiplicative.ofAdd (Point.some 0 0 hxy)) =
      ![scalarClass (A * B) (mul_ne_zero hA hB),
        scalarClass (-A) (neg_ne_zero.mpr hA), scalarClass (-B) (neg_ne_zero.mpr hB)] := by
  letI := splitCurve_isElliptic A B hA hB hAB
  ext i
  change orderedDelta (splitRoots A B) (splitRoots_injective A B hA hB hAB)
    (splitCurve_f_factorization A B)
    (Multiplicative.ofAdd (Point.some (splitRoots A B 0) 0 hxy)) i = _
  rw [orderedDelta_some_at_root _ _ _ 0 hxy i]
  fin_cases i <;> simp [torsionRow, splitRoots]

/-- Complete ordered signed row at the root `A`. -/
theorem splitDelta_at_A (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B)
    (hxy : (splitCurve A B).toAffine.Nonsingular A 0) :
    splitDelta A B hA hB hAB (Multiplicative.ofAdd (Point.some A 0 hxy)) =
      ![scalarClass A hA,
        scalarClass (A * (A-B)) (mul_ne_zero hA (sub_ne_zero.mpr hAB)),
        scalarClass (A-B) (sub_ne_zero.mpr hAB)] := by
  letI := splitCurve_isElliptic A B hA hB hAB
  ext i
  change orderedDelta (splitRoots A B) (splitRoots_injective A B hA hB hAB)
    (splitCurve_f_factorization A B)
    (Multiplicative.ofAdd (Point.some (splitRoots A B 1) 0 hxy)) i = _
  rw [orderedDelta_some_at_root _ _ _ 1 hxy i]
  fin_cases i <;> simp [torsionRow, splitRoots]

/-- Complete ordered signed row at the root `B`. -/
theorem splitDelta_at_B (A B : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B)
    (hxy : (splitCurve A B).toAffine.Nonsingular B 0) :
    splitDelta A B hA hB hAB (Multiplicative.ofAdd (Point.some B 0 hxy)) =
      ![scalarClass B hB, scalarClass (B-A) (sub_ne_zero.mpr hAB.symm),
        scalarClass (B * (B-A)) (mul_ne_zero hB (sub_ne_zero.mpr hAB.symm))] := by
  letI := splitCurve_isElliptic A B hA hB hAB
  ext i
  change orderedDelta (splitRoots A B) (splitRoots_injective A B hA hB hAB)
    (splitCurve_f_factorization A B)
    (Multiplicative.ofAdd (Point.some (splitRoots A B 2) 0 hxy)) i = _
  rw [orderedDelta_some_at_root _ _ _ 2 hxy i]
  fin_cases i <;> simp [torsionRow, splitRoots]

#print axioms splitDelta_at_zero
#print axioms splitDelta_at_A
#print axioms splitDelta_at_B
#print axioms splitRoots_injective
#print axioms splitCurve_f_factorization
#print axioms splitCurve_isElliptic
#print axioms splitEval
#print axioms splitDelta_ker
#print axioms splitDelta_eq_one_iff_double
#print axioms splitDelta_some_of_nonroot

end
end FourCorner.OrderedSplit
