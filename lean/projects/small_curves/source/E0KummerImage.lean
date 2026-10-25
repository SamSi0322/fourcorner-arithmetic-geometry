import SplitCurveOrdered
import SignedSquareClasses
import FourCorner.NineSmallE0
import FourCorner.NineSmallE0Points

open WeierstrassCurve.Affine
namespace FourCorner.NineSmallE0
open FourCorner.OrderedSplit
noncomputable section

def delta : Multiplicative Curve.Point →* (Fin 3 → Units.modPow ℚ 2) :=
  splitDelta (-1) (-4) (by norm_num) (by norm_num) (by norm_num)

def row0 : Fin 3 → Units.modPow ℚ 2 :=
  ![scalarClass 1 (by norm_num), scalarClass 1 (by norm_num), scalarClass 1 (by norm_num)]
def row1 : Fin 3 → Units.modPow ℚ 2 :=
  ![scalarClass (-1) (by norm_num), scalarClass (-3) (by norm_num), scalarClass 3 (by norm_num)]
def row2 : Fin 3 → Units.modPow ℚ 2 :=
  ![scalarClass 2 (by norm_num), scalarClass 3 (by norm_num), scalarClass 6 (by norm_num)]
def row3 : Fin 3 → Units.modPow ℚ 2 :=
  ![scalarClass (-2) (by norm_num), scalarClass (-1) (by norm_num), scalarClass 2 (by norm_num)]

def rows : Finset (Fin 3 → Units.modPow ℚ 2) := by
  classical
  exact {row0, row1, row2, row3}

theorem rows_card_le : rows.card ≤ 4 := by
  classical
  calc
    rows.card ≤ ({row1, row2, row3} : Finset _).card + 1 := Finset.card_insert_le ..
    _ ≤ (({row2, row3} : Finset _).card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le ..) 1
    _ ≤ ((({row3} : Finset _).card + 1) + 1) + 1 := Nat.add_le_add_right
      (Nat.add_le_add_right (Finset.card_insert_le ..) 1) 1
    _ = 4 := by simp

lemma scalar_eq_of_sq (a b q : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a=b*q^2) : scalarClass a ha = scalarClass b hb :=
  (Units.modPow.signedUnits_mk0_eq_iff_exists a b ha hb).mpr ⟨q,h⟩

lemma ordinary_delta_of_squares {x y a b c d e f : ℚ}
    (hxy : Curve.Nonsingular x y) (hx : x ≠ 0) (hx1 : x+1 ≠ 0) (hx4 : x+4 ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (h0 : x=d*a^2) (h1 : x+1=e*b^2) (h4 : x+4=f*c^2) :
    delta (Multiplicative.ofAdd (Point.some x y hxy)) =
      ![scalarClass d hd, scalarClass e he, scalarClass f hf] := by
  have hxA : x ≠ -1 := by intro hz; apply hx1; rw [hz]; norm_num
  have hxB : x ≠ -4 := by intro hz; apply hx4; rw [hz]; norm_num
  rw [delta, splitDelta_some_of_nonroot (-1) (-4) (by norm_num) (by norm_num)
    (by norm_num) hxy hx hxA hxB]
  ext i
  fin_cases i
  · exact scalar_eq_of_sq x d a hx hd h0
  · exact scalar_eq_of_sq _ e b _ he (by simpa using h1)
  · exact scalar_eq_of_sq _ f c _ hf (by simpa using h4)

theorem ordinary_delta_mem {x y : ℚ} (hxy : Curve.Nonsingular x y)
    (hx : x ≠ 0) (hx1 : x+1 ≠ 0) (hx4 : x+4 ≠ 0) :
    delta (Multiplicative.ofAdd (Point.some x y hxy)) ∈ rows := by
  have h : OnCurve x y := by
    simpa [OnCurve] using (splitCurve_equation_iff (-1) (-4) x y).mp hxy.1
  rcases ordinary_row h hx hx1 hx4 with ⟨a,b,c,h0,h1,h4⟩ |
    ⟨a,b,c,h0,h1,h4⟩ | ⟨a,b,c,h0,h1,h4⟩ | ⟨a,b,c,h0,h1,h4⟩
  · have heq : delta (Multiplicative.ofAdd (Point.some x y hxy)) = row0 :=
      ordinary_delta_of_squares hxy hx hx1 hx4 (by norm_num) (by norm_num) (by norm_num)
        (by simpa using h0) (by simpa using h1) (by simpa using h4)
    simp [rows, heq]

  · have heq : delta (Multiplicative.ofAdd (Point.some x y hxy)) = row1 :=
      ordinary_delta_of_squares hxy hx hx1 hx4 (by norm_num) (by norm_num) (by norm_num)
        (by simpa using h0) h1 h4
    simp [rows, heq]
  · have heq : delta (Multiplicative.ofAdd (Point.some x y hxy)) = row2 :=
      ordinary_delta_of_squares hxy hx hx1 hx4 (by norm_num) (by norm_num) (by norm_num) h0 h1 h4
    simp [rows, heq]
  · have heq : delta (Multiplicative.ofAdd (Point.some x y hxy)) = row3 :=
      ordinary_delta_of_squares hxy hx hx1 hx4 (by norm_num) (by norm_num) (by norm_num)
        h0 (by simpa using h1) h4
    simp [rows, heq]

lemma scalar_one : scalarClass (1 : ℚ) (by norm_num) = 1 := by
  simp [scalarClass]

lemma delta_zero_row : delta (Multiplicative.ofAdd (0 : Curve.Point)) = row0 := by
  change delta 1 = row0
  rw [map_one]
  ext i
  fin_cases i <;> simp [row0, scalar_one]

local instance curve_elliptic : Curve.IsElliptic :=
  splitCurve_isElliptic (-1) (-4) (by norm_num) (by norm_num) (by norm_num)

lemma root_delta_coordinate {x y t : ℚ} (hxy : Curve.Nonsingular x y)
    (hx : Curve.f.eval x = 0) (i : Fin 3) (ht : t ≠ 0)
    (hval : x - splitRoots (-1) (-4) i +
      (Curve.fCofactor x).eval (splitRoots (-1) (-4) i) = t) :
    delta (Multiplicative.ofAdd (Point.some x y hxy)) i = scalarClass t ht := by
  exact orderedDelta_some_of_root (splitRoots (-1) (-4))
    (splitRoots_injective (-1) (-4) (by norm_num) (by norm_num) (by norm_num))
    (splitCurve_f_factorization (-1) (-4)) hxy hx i ht hval

lemma delta_root_zero {y : ℚ} (hxy : Curve.Nonsingular 0 y) :
    delta (Multiplicative.ofAdd (Point.some 0 y hxy)) = row0 := by
  have hx : Curve.f.eval 0 = 0 := by norm_num [f, splitCurve]
  ext i
  fin_cases i
  · exact (root_delta_coordinate hxy hx 0 (by norm_num : (4 : ℚ) ≠ 0)
      (by norm_num [splitRoots, fCofactor, splitCurve, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])).trans
      (scalar_eq_of_sq 4 1 2 (by norm_num) (by norm_num) (by norm_num))
  · exact root_delta_coordinate hxy hx 1 (by norm_num : (1 : ℚ) ≠ 0)
      (by norm_num [splitRoots, fCofactor, splitCurve, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])
  · exact (root_delta_coordinate hxy hx 2 (by norm_num : (4 : ℚ) ≠ 0)
      (by norm_num [splitRoots, fCofactor, splitCurve, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])).trans
      (scalar_eq_of_sq 4 1 2 (by norm_num) (by norm_num) (by norm_num))

lemma delta_root_neg_one {y : ℚ} (hxy : Curve.Nonsingular (-1) y) :
    delta (Multiplicative.ofAdd (Point.some (-1) y hxy)) = row1 := by
  have hx : Curve.f.eval (-1) = 0 := by norm_num [f, splitCurve]
  ext i
  fin_cases i
  · exact root_delta_coordinate hxy hx 0 (by norm_num : (-1 : ℚ) ≠ 0)
      (by norm_num [splitRoots, fCofactor, splitCurve, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])
  · exact root_delta_coordinate hxy hx 1 (by norm_num : (-3 : ℚ) ≠ 0)
      (by norm_num [splitRoots, fCofactor, splitCurve, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])
  · exact root_delta_coordinate hxy hx 2 (by norm_num : (3 : ℚ) ≠ 0)
      (by norm_num [splitRoots, fCofactor, splitCurve, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])

lemma delta_root_neg_four {y : ℚ} (hxy : Curve.Nonsingular (-4) y) :
    delta (Multiplicative.ofAdd (Point.some (-4) y hxy)) = row1 := by
  have hx : Curve.f.eval (-4) = 0 := by norm_num [f, splitCurve]
  ext i
  fin_cases i
  · exact (root_delta_coordinate hxy hx 0 (by norm_num : (-4 : ℚ) ≠ 0)
      (by norm_num [splitRoots, fCofactor, splitCurve, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])).trans
      (scalar_eq_of_sq (-4) (-1) 2 (by norm_num) (by norm_num) (by norm_num))
  · exact root_delta_coordinate hxy hx 1 (by norm_num : (-3 : ℚ) ≠ 0)
      (by norm_num [splitRoots, fCofactor, splitCurve, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])
  · exact (root_delta_coordinate hxy hx 2 (by norm_num : (12 : ℚ) ≠ 0)
      (by norm_num [splitRoots, fCofactor, splitCurve, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])).trans
      (scalar_eq_of_sq 12 3 2 (by norm_num) (by norm_num) (by norm_num))

/-- Complete image bound, including infinity and every two-torsion point. -/
theorem delta_mem (P : Curve.Point) : delta (Multiplicative.ofAdd P) ∈ rows := by
  cases P with
  | zero =>
      change delta (Multiplicative.ofAdd (0 : Curve.Point)) ∈ rows
      rw [delta_zero_row]
      simp [rows]
  | some x y hxy =>
      by_cases hx : x=0
      · subst x; rw [delta_root_zero]; simp [rows]
      by_cases hx1 : x+1=0
      · have hz : x= -1 := by linarith
        subst x; rw [delta_root_neg_one]; simp [rows]
      by_cases hx4 : x+4=0
      · have hz : x= -4 := by linarith
        subst x; rw [delta_root_neg_four]; simp [rows]
      exact ordinary_delta_mem hxy hx hx1 hx4

end
end FourCorner.NineSmallE0

#print axioms FourCorner.NineSmallE0.ordinary_delta_mem
#print axioms FourCorner.NineSmallE0.delta_mem
